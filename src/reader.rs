use half::f16;
use std::io::{Read, Result, Seek};

use crate::Endian;

pub trait BinaryReader {
    fn read_bool(&mut self) -> Result<bool>;
    fn read_char(&mut self) -> Result<char>;

    fn read_u8(&mut self) -> Result<u8>;
    fn read_u16(&mut self) -> Result<u16>;
    fn read_u32(&mut self) -> Result<u32>;
    fn read_u64(&mut self) -> Result<u64>;

    fn read_i8(&mut self) -> Result<i8>;
    fn read_i16(&mut self) -> Result<i16>;
    fn read_i32(&mut self) -> Result<i32>;
    fn read_i64(&mut self) -> Result<i64>;

    fn read_f16(&mut self) -> Result<f32>;
    fn read_f32(&mut self) -> Result<f32>;
    fn read_f64(&mut self) -> Result<f64>;

    fn read_cstr(&mut self) -> Result<String>;

    fn read_str(&mut self, len: Option<usize>) -> Result<String>;
    fn read_bytes(&mut self, len: Option<usize>) -> Result<Vec<u8>>;

    fn read_bool_array(&mut self, len: Option<usize>) -> Result<Vec<bool>>;
    fn read_char_array(&mut self, len: Option<usize>) -> Result<Vec<char>>;
    fn read_u8_array(&mut self, len: Option<usize>) -> Result<Vec<u8>>;
    fn read_u16_array(&mut self, len: Option<usize>) -> Result<Vec<u16>>;
    fn read_u32_array(&mut self, len: Option<usize>) -> Result<Vec<u32>>;
    fn read_u64_array(&mut self, len: Option<usize>) -> Result<Vec<u64>>;
    fn read_i8_array(&mut self, len: Option<usize>) -> Result<Vec<i8>>;
    fn read_i16_array(&mut self, len: Option<usize>) -> Result<Vec<i16>>;
    fn read_i32_array(&mut self, len: Option<usize>) -> Result<Vec<i32>>;
    fn read_i64_array(&mut self, len: Option<usize>) -> Result<Vec<i64>>;
    fn read_f16_array(&mut self, len: Option<usize>) -> Result<Vec<f32>>;
    fn read_f32_array(&mut self, len: Option<usize>) -> Result<Vec<f32>>;
    fn read_f64_array(&mut self, len: Option<usize>) -> Result<Vec<f64>>;
    fn read_cstr_array(&mut self, len: Option<usize>) -> Result<Vec<String>>;
    fn read_str_array(&mut self, len: Option<usize>) -> Result<Vec<String>>;
    fn read_bytes_array(&mut self, len: Option<usize>) -> Result<Vec<Vec<u8>>>;
}

macro_rules! build_read_array_fn {
    ($name:ident, $func:ident, $type:ty) => {
        fn $name(&mut self, len: Option<usize>) -> Result<Vec<$type>> {
            let array_len;
            if len.is_none() {
                array_len = self.read_u32()? as usize;
            } else {
                array_len = len.unwrap();
            }
            let mut buf: Vec<$type> = Vec::with_capacity(array_len);
            for i in 0..array_len {
                buf[i] = self.$func()?;
            }
            Ok(buf)
        }
    };
}

macro_rules! build_read_array_fn_arg {
    ($name:ident, $func:ident, $type:ty) => {
        fn $name(&mut self, len: Option<usize>) -> Result<Vec<$type>> {
            let array_len;
            if len.is_none() {
                array_len = self.read_u32()? as usize;
            } else {
                array_len = len.unwrap();
            }
            let mut buf: Vec<$type> = Vec::with_capacity(array_len);
            for i in 0..array_len {
                buf[i] = self.$func(None)?;
            }
            Ok(buf)
        }
    };
}

macro_rules! build_read_fn_generic {
    () => {
        fn read_bool(&mut self) -> Result<bool> {
            return Ok(self.read_u8()? != 0);
        }
        fn read_char(&mut self) -> Result<char> {
            return Ok(self.read_u8()? as char);
        }
        fn read_cstr(&mut self) -> Result<String> {
            let mut buf: Vec<u8> = Vec::new();
            let mut c: u8;
            loop {
                c = self.read_u8()?;
                if c == 0 {
                    break;
                }
                buf.push(c as u8);
            }
            Ok(String::from_utf8(buf).unwrap())
        }
        fn read_str(&mut self, len: Option<usize>) -> Result<String> {
            Ok(String::from_utf8(self.read_bytes(len)?).unwrap())
        }

        fn read_bytes(&mut self, len: Option<usize>) -> Result<Vec<u8>> {
            let str_len;
            if len.is_none() {
                str_len = self.read_u32()? as usize;
            } else {
                str_len = len.unwrap();
            }
            let mut buf = vec![0u8; str_len];
            self.inner.read_exact(&mut buf)?;
            Ok(buf)
        }

        fn read_f16(&mut self) -> Result<f32> {
            Ok(f16::from_bits(self.read_u16()?).to_f32())
        }

        build_read_array_fn!(read_bool_array, read_bool, bool);
        build_read_array_fn!(read_char_array, read_char, char);
        build_read_array_fn!(read_f16_array, read_f16, f32);
        build_read_array_fn!(read_cstr_array, read_cstr, String);
        build_read_array_fn_arg!(read_str_array, read_str, String);
        build_read_array_fn_arg!(read_bytes_array, read_bytes, Vec<u8>);
    };
}

macro_rules! build_read_fn_ve {
    ($type:ty) => {
        paste::item! {
            fn [< read_ $type >] (&mut self) -> Result<$type> {
                let mut buf = [0u8; std::mem::size_of::<$type>()];
                self.inner.read_exact(&mut buf)?;
                match self.endian {
                    Endian::Little => Ok(<$type>::from_le_bytes(buf)),
                    Endian::Big => Ok(<$type>::from_be_bytes(buf)),
                }
            }
        }
        paste::item! {
            fn [< read_ $type _array >] (&mut self, len: Option<usize>) -> Result<Vec<$type>> {
                let array_len;
                if len.is_none() {
                    array_len = self.read_u32()? as usize;
                } else {
                    array_len = len.unwrap();
                }
                let raw_len = array_len * std::mem::size_of::<$type>();
                let raw_buf = vec![0u8; raw_len];
                let mut buf: Vec<$type> = Vec::with_capacity(array_len);
                match self.endian {
                    Endian::Little => {
                        for i in 0..array_len {
                            let start = i * std::mem::size_of::<$type>();
                            let end = start + std::mem::size_of::<$type>();
                            let slice = &raw_buf[start..end];
                            buf[i] = <$type>::from_le_bytes(slice.try_into().unwrap());
                        }
                    }
                    Endian::Big => {
                        for i in 0..array_len {
                            let start = i * std::mem::size_of::<$type>();
                            let end = start + std::mem::size_of::<$type>();
                            let slice = &raw_buf[start..end];
                            buf[i] = <$type>::from_be_bytes(slice.try_into().unwrap());
                        }
                    }
                }
                Ok(buf)
            }
        }
    };
}

pub struct BinaryReaderVE<R> {
    pub inner: R,
    pub endian: Endian,
}

impl<R: Read> BinaryReaderVE<R> {
    pub fn new(inner: R, endian: Endian) -> Self {
        Self { inner, endian }
    }
}

impl<R: Read> BinaryReader for BinaryReaderVE<R> {
    build_read_fn_generic!();
    build_read_fn_ve!(u8);
    build_read_fn_ve!(u16);
    build_read_fn_ve!(u32);
    build_read_fn_ve!(u64);

    build_read_fn_ve!(i8);
    build_read_fn_ve!(i16);
    build_read_fn_ve!(i32);
    build_read_fn_ve!(i64);

    build_read_fn_ve!(f32);
    build_read_fn_ve!(f64);
}

macro_rules! build_read_fn_le {
    ($type:ty) => {
        paste::item! {
            fn [< read_ $type >] (&mut self) -> Result<$type> {
                let mut buf = [0u8; std::mem::size_of::<$type>()];
                self.inner.read_exact(&mut buf)?;
                Ok(<$type>::from_le_bytes(buf))
            }
        }
        paste::item! {
            fn [< read_ $type _array >] (&mut self, len: Option<usize>) -> Result<Vec<$type>> {
                let array_len;
                if len.is_none() {
                    array_len = self.read_u32()? as usize;
                } else {
                    array_len = len.unwrap();
                }
                let raw_len = array_len * std::mem::size_of::<$type>();
                let raw_buf = vec![0u8; raw_len];
                let mut buf: Vec<$type> = Vec::with_capacity(array_len);
                for i in 0..array_len {
                    let start = i * std::mem::size_of::<$type>();
                    let end = start + std::mem::size_of::<$type>();
                    let slice = &raw_buf[start..end];
                    buf[i] = <$type>::from_le_bytes(slice.try_into().unwrap());
                }
                Ok(buf)
            }
        }
    };
}

pub struct BinaryReaderLE<R> {
    pub inner: R,
}

impl<R: Read> BinaryReaderLE<R> {
    pub fn new(inner: R) -> Self {
        Self { inner }
    }
}

impl<R: Read> BinaryReader for BinaryReaderLE<R> {
    build_read_fn_generic!();
    build_read_fn_le!(u8);
    build_read_fn_le!(u16);
    build_read_fn_le!(u32);
    build_read_fn_le!(u64);

    build_read_fn_le!(i8);
    build_read_fn_le!(i16);
    build_read_fn_le!(i32);
    build_read_fn_le!(i64);

    build_read_fn_le!(f32);
    build_read_fn_le!(f64);
}

macro_rules! build_read_fn_be {
    ($type:ty) => {
        paste::item! {
            fn [< read_ $type >] (&mut self) -> Result<$type> {
                let mut buf = [0u8; std::mem::size_of::<$type>()];
                self.inner.read_exact(&mut buf)?;
                Ok(<$type>::from_be_bytes(buf))
            }
        }
        paste::item! {
            fn [< read_ $type _array >] (&mut self, len: Option<usize>) -> Result<Vec<$type>> {
                let array_len;
                if len.is_none() {
                    array_len = self.read_u32()? as usize;
                } else {
                    array_len = len.unwrap();
                }
                let raw_len = array_len * std::mem::size_of::<$type>();
                let raw_buf = vec![0u8; raw_len];
                let mut buf: Vec<$type> = Vec::with_capacity(array_len);
                for i in 0..array_len {
                    let start = i * std::mem::size_of::<$type>();
                    let end = start + std::mem::size_of::<$type>();
                    let slice = &raw_buf[start..end];
                    buf[i] = <$type>::from_be_bytes(slice.try_into().unwrap());
                }
                Ok(buf)
            }
        }
    };
}

pub struct BinaryReaderBE<R> {
    pub inner: R,
}

impl<R: Read> BinaryReaderBE<R> {
    pub fn new(inner: R) -> Self {
        Self { inner }
    }
}

impl<R: Read> BinaryReader for BinaryReaderBE<R> {
    build_read_fn_generic!();
    build_read_fn_be!(u8);
    build_read_fn_be!(u16);
    build_read_fn_be!(u32);

    build_read_fn_be!(u64);
    build_read_fn_be!(i8);
    build_read_fn_be!(i16);

    build_read_fn_be!(i32);
    build_read_fn_be!(i64);

    build_read_fn_be!(f32);
    build_read_fn_be!(f64);
}

macro_rules! build_align_fn {
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
}

build_align_fn!(BinaryReaderLE);
build_align_fn!(BinaryReaderBE);
build_align_fn!(BinaryReaderVE);

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    fn test_read_unsigned(reader: &mut impl (BinaryReader)) -> Result<()> {
        assert_eq!(reader.read_u8()?, 0x1);
        assert_eq!(reader.read_u16()?, 0x1234);
        assert_eq!(reader.read_u32()?, 0x12345678);
        assert_eq!(reader.read_u64()?, 0x1234567890123456);
        Ok(())
    }

    fn test_read_signed(reader: &mut dyn BinaryReader) -> Result<()> {
        assert_eq!(reader.read_i8()?, 0x1);
        assert_eq!(reader.read_i16()?, -0x1234);
        assert_eq!(reader.read_i32()?, 0x12345678);
        assert_eq!(reader.read_i64()?, -0x1234567890123456);
        Ok(())
    }

    fn test_read_float(reader: &mut dyn BinaryReader) -> Result<()> {
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
