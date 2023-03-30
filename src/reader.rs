use byteorder::{BigEndian, LittleEndian, ReadBytesExt};
use half::f16;
use std::io::{Read, Result, Seek};

use crate::Endian;

macro_rules! read_method{
    (array $typ:ty, $size:expr) => {
        paste::item! {
            #[doc = "Reads an array of [`" $typ "`]s (" $size " byte(s) each). If len is none the reader will determine the length by reading it."]
            fn [< read_ $typ _array >] (&mut self, len: Option<usize>) -> Result<Vec<$typ>>{
                let len = len.unwrap_or_else(|| self.read_array_len().unwrap());
                Ok(
                    (0..len)
                        .map(|_| self.[< read_ $typ >]())
                        .collect::<Result<Vec<$typ>>>()?
                )
            }
        }
    };

    ($typ:ty, $size:expr) => {
        paste::item! {
            #[doc = "Reads a [`" $typ "`] (" $size " byte(s))."]
            fn [< read_ $typ >] (&mut self) -> Result<$typ>;
        }

        read_method!(array $typ, $size);
    };
}

pub trait BinaryRead {
    /// Reads a bool (1 byte).
    fn read_bool(&mut self) -> Result<bool> {
        Ok(self.read_u8()? == 1)
    }
    read_method!(array bool, 1);

    /// Reads a char (1 byte).
    fn read_char(&mut self) -> Result<char> {
        Ok(self.read_u8()? as char)
    }
    read_method!(array char, 1);

    read_method!(u8, 1);
    read_method!(u16, 2);
    read_method!(u32, 4);
    read_method!(u64, 8);

    read_method!(i8, 1);
    read_method!(i16, 2);
    read_method!(i32, 4);
    read_method!(i64, 8);

    /// Reads a [`f16`] (2 bytes).
    fn read_f16(&mut self) -> Result<f32> {
        Ok(f16::from_bits(self.read_u16()?).to_f32())
    }
    /// Reads an array of [`f16`]s (2 byte(s) each). If len is none the reader will determine the length by reading it.
    fn read_f16_array(&mut self, len: Option<usize>) -> Result<Vec<f32>> {
        let len = len.unwrap_or_else(|| self.read_array_len().unwrap());
        // use read_u16_array to benefit from the byteorder read optimizations
        Ok(self
            .read_u16_array(Some(len))?
            .iter()
            .map(|x| f16::from_bits(*x).to_f32())
            .collect())
    }

    read_method!(f32, 4);
    read_method!(f64, 8);

    /// Reads a c-string (null terminated string).
    fn read_cstr(&mut self) -> Result<String> {
        let mut bytes = Vec::new();
        loop {
            let byte = self.read_u8()?;
            if byte == 0 {
                break;
            }
            bytes.push(byte);
        }
        Ok(String::from_utf8(bytes).unwrap())
    }

    /// Reads a string. If len is none the reader will determine the length by reading it.
    fn read_str(&mut self, len: Option<usize>) -> Result<String> {
        Ok(String::from_utf8(self.read_bytes(len)?).unwrap())
    }
    /// Reads bytes as `Vec<u8>`. If len is none the reader will determine the length by reading it.
    fn read_bytes(&mut self, len: Option<usize>) -> Result<Vec<u8>> {
        self.read_u8_array(len)
    }

    /// Reads the length for an array.
    fn read_array_len(&mut self) -> Result<usize>;

    /// Reads an array of c-strings. If len is none the reader will determine the length by reading it.
    fn read_cstr_array(&mut self, len: Option<usize>) -> Result<Vec<String>> {
        let len = len.unwrap_or_else(|| self.read_array_len().unwrap());
        Ok((0..len)
            .map(|_| self.read_cstr())
            .collect::<Result<Vec<String>>>()?)
    }
    /// Reads an array of strings. If len is none the reader will determine the length by reading it.
    fn read_str_array(&mut self, len: Option<usize>) -> Result<Vec<String>> {
        let len = len.unwrap_or_else(|| self.read_array_len().unwrap());
        Ok((0..len)
            .map(|_| self.read_str(None))
            .collect::<Result<Vec<String>>>()?)
    }
    /// Reads an array of bytes. If len is none the reader will determine the length by reading it.
    fn read_bytes_array(&mut self, len: Option<usize>) -> Result<Vec<Vec<u8>>> {
        let len = len.unwrap_or_else(|| self.read_array_len().unwrap());
        Ok((0..len)
            .map(|_| self.read_bytes(None))
            .collect::<Result<Vec<Vec<u8>>>>()?)
    }
}

pub trait BinaryReadAlign: BinaryRead + Seek {
    /// Align the reader to the given alignment and return the aligned position.
    fn align(&mut self, alignment: usize) -> Result<usize>;
    /// Align the reader to 4 bytes.
    fn align4(&mut self) -> Result<usize> {
        self.align(4)
    }
    /// Align the reader to 8 bytes.
    fn align8(&mut self) -> Result<usize> {
        self.align(8)
    }
    /// Align the reader to 16 bytes.
    fn align16(&mut self) -> Result<usize> {
        self.align(16)
    }
}

// =================================================================================================
//
// Method implementation macros for BinaryReader structs
//
// =================================================================================================

macro_rules! implement_generic_methods {
    () => {
        fn read_u8(&mut self) -> Result<u8> {
            self.inner.read_u8()
        }

        fn read_u8_array(&mut self, len: Option<usize>) -> Result<Vec<u8>> {
            let len = len.unwrap_or_else(|| self.read_array_len().unwrap());
            let mut buf = vec![0u8; len];
            self.inner.read_exact(&mut buf)?;
            Ok(buf)
        }

        fn read_i8(&mut self) -> Result<i8> {
            self.inner.read_i8()
        }

        fn read_i8_array(&mut self, len: Option<usize>) -> Result<Vec<i8>> {
            let len = len.unwrap_or_else(|| self.read_array_len().unwrap());
            let mut buf = vec![0i8; len];
            self.inner.read_i8_into(&mut buf)?;
            Ok(buf)
        }

        fn read_array_len(&mut self) -> Result<usize> {
            Ok(self.read_u32()? as usize)
        }
    };
}

/// Implement a read and read_array method for a type with the given from_(b/l)e_bytes method.
macro_rules! implement_read_e_method {
    ($endian:expr, $type:ty) => {
        paste::item! {
            fn [< read_ $type >] (&mut self) -> Result<$type> {
                self.inner.[<read_ $type>]::<$endian>()
            }
        }
        paste::item! {
            fn [< read_ $type _array >] (&mut self, len: Option<usize>) -> Result<Vec<$type>> {
                let len = len.unwrap_or_else(|| self.read_array_len().unwrap());
                let mut ret: Vec<$type> = Vec::with_capacity(len);
                self.inner.[<read_ $type _into>]::<$endian>(ret.as_mut_slice()).unwrap();
                Ok(ret)
            }
        }
    };

    ($endian:expr, $($typ:ty),+) => (
        $(implement_read_e_method!($endian, $typ);)+
    )
}

/// Implement a read and read_array method for a type with a variable endian.
macro_rules! implement_read_ve_method {
    ($type:ty) => {
        // implement read_$type
        paste::item! {
            fn [< read_ $type >] (&mut self) -> Result<$type> {
                match self.endian {
                    Endian::Little => self.inner.[<read_ $type>]::<LittleEndian>(),
                    Endian::Big => self.inner.[<read_ $type>]::<BigEndian>(),
                }
            }
        }
        paste::item! {
            fn [< read_ $type _array >] (&mut self, len: Option<usize>) -> Result<Vec<$type>> {
                let len = len.unwrap_or_else(|| self.read_array_len().unwrap());
                let mut ret: Vec<$type> = Vec::with_capacity(len);
                match self.endian {
                    Endian::Little => {
                        self.inner.[<read_ $type _into>]::<LittleEndian>(ret.as_mut_slice()).unwrap();
                    }
                    Endian::Big => {
                        self.inner.[<read_ $type _into>]::<BigEndian>(ret.as_mut_slice()).unwrap();
                    }
                }
                Ok(ret)
            }
        }
    };

    ($($typ:ty),+) => (
        $(implement_read_ve_method!($typ);)+
    )
}

macro_rules! generate_BinaryReaderE {
    ($name: ident, $byteorder: ident) => {
        pub struct $name<R> {
            pub inner: R,
        }

        impl<R: Read> $name<R> {
            pub fn new(inner: R) -> Self {
                Self { inner }
            }
        }

        impl<R: Read> BinaryRead for $name<R> {
            implement_generic_methods!();
            implement_read_e_method!($byteorder, u16, u32, u64, i16, i32, i64, f32, f64);
        }
    };
}

macro_rules! implement_align_method {
    ($struct_:ident) => {
        impl<R: Seek> $struct_<R> {
            pub fn align(&mut self, alignment: usize) -> Result<()> {
                let pos = self.inner.seek(std::io::SeekFrom::Current(0))?;
                let rem = pos % alignment as u64;
                if rem != 0 {
                    self.inner.seek(std::io::SeekFrom::Current(rem as i64))?;
                }
                Ok(())
            }
        }

        impl<R: Seek> Seek for $struct_<R> {
            fn seek(&mut self, pos: std::io::SeekFrom) -> Result<u64> {
                self.inner.seek(pos)
            }

            fn stream_position(&mut self) -> Result<u64> {
                self.inner.stream_position()
            }
        }
    };

    ($($typ:ident),+) => (
        $(implement_align_method!($typ);)+
    )
}

// =================================================================================================
//
// BinaryReader implementations
//
// =================================================================================================

pub struct BinaryReaderVE<R> {
    pub inner: R,
    pub endian: Endian,
}

impl<R: Read> BinaryReaderVE<R> {
    pub fn new(inner: R, endian: Endian) -> Self {
        Self { inner, endian }
    }
}

impl<R: Read> BinaryRead for BinaryReaderVE<R> {
    implement_generic_methods!();
    implement_read_ve_method!(u16, u32, u64, i16, i32, i64, f32, f64);
}

generate_BinaryReaderE!(BinaryReaderLE, LittleEndian);
generate_BinaryReaderE!(BinaryReaderBE, BigEndian);
implement_align_method!(BinaryReaderLE, BinaryReaderBE, BinaryReaderVE);

// =================================================================================================
//
// Tests
//
// =================================================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    fn test_read_unsigned(reader: &mut impl (BinaryRead)) -> Result<()> {
        assert_eq!(reader.read_u8()?, 0x1);
        assert_eq!(reader.read_u16()?, 0x1234);
        assert_eq!(reader.read_u32()?, 0x12345678);
        assert_eq!(reader.read_u64()?, 0x1234567890123456);
        Ok(())
    }

    fn test_read_signed(reader: &mut dyn BinaryRead) -> Result<()> {
        assert_eq!(reader.read_i8()?, 0x1);
        assert_eq!(reader.read_i16()?, -0x1234);
        assert_eq!(reader.read_i32()?, 0x12345678);
        assert_eq!(reader.read_i64()?, -0x1234567890123456);
        Ok(())
    }

    fn test_read_float(reader: &mut dyn BinaryRead) -> Result<()> {
        assert_eq!(reader.read_f16()?, f16::from_f32(0.16).to_f32());
        assert_eq!(reader.read_f32()?, -0.32);
        assert_eq!(reader.read_f64()?, 0.64);
        Ok(())
    }

    #[test]
    pub fn test_binary_reader() {
        let mut reader = BinaryReaderVE::new(
            Cursor::new(&b"\x014\x12xV4\x12V4\x12\x90xV4\x12"[..]),
            Endian::Little,
        );
        test_read_unsigned(&mut reader).unwrap();

        let mut reader = BinaryReaderVE::new(
            Cursor::new(&b"\x01\xcc\xedxV4\x12\xaa\xcb\xedo\x87\xa9\xcb\xed"[..]),
            Endian::Little,
        );
        test_read_signed(&mut reader).unwrap();

        let mut reader = BinaryReaderVE::new(
            Cursor::new(&b"\x1f1\n\xd7\xa3\xbe{\x14\xaeG\xe1z\xe4?"[..]),
            Endian::Little,
        );
        test_read_float(&mut reader).unwrap();

        let mut reader = BinaryReaderVE::new(
            Cursor::new(&b"\x01\x124\x124Vx\x124Vx\x90\x124V"[..]),
            Endian::Big,
        );
        test_read_unsigned(&mut reader).unwrap();

        let mut reader = BinaryReaderVE::new(
            Cursor::new(&b"\x01\xed\xcc\x124Vx\xed\xcb\xa9\x87o\xed\xcb\xaa"[..]),
            Endian::Big,
        );
        test_read_signed(&mut reader).unwrap();

        let mut reader = BinaryReaderVE::new(
            Cursor::new(&b"1\x1f\xbe\xa3\xd7\n?\xe4z\xe1G\xae\x14{"[..]),
            Endian::Big,
        );
        test_read_float(&mut reader).unwrap();
    }

    #[test]
    pub fn test_binary_reader_le() {
        let mut reader =
            BinaryReaderLE::new(Cursor::new(&b"\x014\x12xV4\x12V4\x12\x90xV4\x12"[..]));
        test_read_unsigned(&mut reader).unwrap();

        let mut reader = BinaryReaderLE::new(Cursor::new(
            &b"\x01\xcc\xedxV4\x12\xaa\xcb\xedo\x87\xa9\xcb\xed"[..],
        ));
        test_read_signed(&mut reader).unwrap();

        let mut reader =
            BinaryReaderLE::new(Cursor::new(&b"\x1f1\n\xd7\xa3\xbe{\x14\xaeG\xe1z\xe4?"[..]));
        test_read_float(&mut reader).unwrap();
    }

    #[test]
    pub fn test_binary_reader_be() {
        let mut reader =
            BinaryReaderBE::new(Cursor::new(&b"\x01\x124\x124Vx\x124Vx\x90\x124V"[..]));
        test_read_unsigned(&mut reader).unwrap();

        let mut reader = BinaryReaderBE::new(Cursor::new(
            &b"\x01\xed\xcc\x124Vx\xed\xcb\xa9\x87o\xed\xcb\xaa"[..],
        ));
        test_read_signed(&mut reader).unwrap();

        let mut reader =
            BinaryReaderBE::new(Cursor::new(&b"1\x1f\xbe\xa3\xd7\n?\xe4z\xe1G\xae\x14{"[..]));
        test_read_float(&mut reader).unwrap();
    }
}
