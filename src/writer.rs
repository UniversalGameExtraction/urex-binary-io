use half::f16;
use std::io::{Result, Seek, Write};

use crate::Endian;

pub trait BinaryWrite {
    /// Writes a bool to the internal stream.  
    fn write_bool(&mut self, value: bool) -> Result<()>;
    /// Writes a char to the internal stream.
    fn write_char(&mut self, value: char) -> Result<()>;

    /// Writes a u8 to the internal stream.
    fn write_u8(&mut self, value: u8) -> Result<()>;
    /// Writes a u16 to the internal stream.
    fn write_u16(&mut self, value: u16) -> Result<()>;
    /// Writes a u32 to the internal stream.
    fn write_u32(&mut self, value: u32) -> Result<()>;
    /// Writes a u64 to the internal stream.
    fn write_u64(&mut self, value: u64) -> Result<()>;

    /// Writes a i8 to the internal stream.
    fn write_i8(&mut self, value: i8) -> Result<()>;
    /// Writes a i16 to the internal stream.
    fn write_i16(&mut self, value: i16) -> Result<()>;
    /// Writes a i32 to the internal stream.
    fn write_i32(&mut self, value: i32) -> Result<()>;
    /// Writes a i64 to the internal stream.
    fn write_i64(&mut self, value: i64) -> Result<()>;

    /// Writes a f16 to the internal stream.
    fn write_f16(&mut self, value: f32) -> Result<()>;
    /// Writes a f32 to the internal stream.
    fn write_f32(&mut self, value: f32) -> Result<()>;
    /// Writes a f64 to the internal stream.
    fn write_f64(&mut self, value: f64) -> Result<()>;

    /// Writes a str as c-string (null-terminated) to the internal stream.
    fn write_cstr(&mut self, value: &str) -> Result<()>;
    /// Writes a str to the internal stream. If `write_len` is `Some(true)`, the length of the string will be written before the string itself.
    fn write_str(&mut self, value: &str, write_len: Option<bool>) -> Result<()>;
    /// Writes a byte slice to the internal stream. If `write_len` is `Some(true)`, the length of the byte slice will be written before the byte slice itself.
    fn write_bytes(&mut self, value: &[u8], write_len: Option<bool>) -> Result<()>;

    /// Writes a bool array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_bool_array(&mut self, value: Vec<bool>, write_len: Option<bool>) -> Result<()>;
    /// Writes a char array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_char_array(&mut self, value: Vec<char>, write_len: Option<bool>) -> Result<()>;
    /// Writes a u8 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_u8_array(&mut self, value: Vec<u8>, write_len: Option<bool>) -> Result<()>;
    /// Writes a u16 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_u16_array(&mut self, value: Vec<u16>, write_len: Option<bool>) -> Result<()>;
    /// Writes a u32 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_u32_array(&mut self, value: Vec<u32>, write_len: Option<bool>) -> Result<()>;
    /// Writes a u64 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_u64_array(&mut self, value: Vec<u64>, write_len: Option<bool>) -> Result<()>;
    /// Writes a i8 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_i8_array(&mut self, value: Vec<i8>, write_len: Option<bool>) -> Result<()>;
    /// Writes a i16 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_i16_array(&mut self, value: Vec<i16>, write_len: Option<bool>) -> Result<()>;
    /// Writes a i32 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_i32_array(&mut self, value: Vec<i32>, write_len: Option<bool>) -> Result<()>;
    /// Writes a i64 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_i64_array(&mut self, value: Vec<i64>, write_len: Option<bool>) -> Result<()>;
    /// Writes a f16 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_f16_array(&mut self, value: Vec<f32>, write_len: Option<bool>) -> Result<()>;
    /// Writes a f32 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_f32_array(&mut self, value: Vec<f32>, write_len: Option<bool>) -> Result<()>;
    /// Writes a f64 array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_f64_array(&mut self, value: Vec<f64>, write_len: Option<bool>) -> Result<()>;
    /// Writes a str array as c-strings (null-terminated) to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_cstr_array(&mut self, value: Vec<&str>, write_len: Option<bool>) -> Result<()>;
    /// Writes a str array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_str_array(&mut self, value: Vec<&str>, write_len: Option<bool>) -> Result<()>;
    /// Writes a byte slice array to the internal stream. If `write_len` is `Some(true)`, the length of the array will be written before the array itself.
    fn write_bytes_array(&mut self, value: Vec<&[u8]>, write_len: Option<bool>) -> Result<()>;
}

pub trait BinaryWriteAlign: BinaryWrite + Seek {
    /// Align the reader to the given alignment.
    fn align(&mut self, alignment: usize) -> Result<()>;
    fn align4(&mut self) -> Result<()> {
        self.align(4)
    }
    fn align8(&mut self) -> Result<()> {
        self.align(8)
    }
    fn align16(&mut self) -> Result<()> {
        self.align(16)
    }
}

macro_rules! build_write_array_fn {
    ($name:ident, $func:ident, $type:ty) => {
        fn $name(&mut self, value: Vec<$type>, write_len: Option<bool>) -> Result<()> {
            if write_len.is_none() || write_len.unwrap() {
                self.write_u32(value.len() as u32)?;
            }
            value.iter().for_each(|v| {
                self.$func(*v).unwrap();
            });
            Ok(())
        }
    };
}

macro_rules! build_write_array_fn_arg {
    ($name:ident, $func:ident, $type:ty) => {
        fn $name(&mut self, value: Vec<$type>, write_len: Option<bool>) -> Result<()> {
            if write_len.is_none() || write_len.unwrap() {
                self.write_u32(value.len() as u32)?;
            }
            value.iter().for_each(|v| {
                self.$func(v, Some(true)).unwrap();
            });
            Ok(())
        }
    };
}

macro_rules! write_fn_generic {
    () => {
        fn write_bool(&mut self, value: bool) -> Result<()> {
            self.inner.write_all(&[value as u8])
        }

        fn write_char(&mut self, value: char) -> Result<()> {
            self.inner.write_all(&[value as u8])
        }

        fn write_f16(&mut self, value: f32) -> Result<()> {
            let value_f16 = f16::from_f32(value);
            self.write_u16(value_f16.to_bits())
        }

        fn write_cstr(&mut self, value: &str) -> Result<()> {
            self.inner.write_all(value.as_bytes())?;
            self.inner.write_all(&[0u8])
        }

        fn write_str(&mut self, value: &str, write_len: Option<bool>) -> Result<()> {
            if write_len.is_none() || write_len.unwrap() {
                let str_len: u32 = value.len() as u32;
                self.write_u32(str_len)?;
            }
            self.inner.write_all(value.as_bytes())
        }

        fn write_bytes(&mut self, value: &[u8], write_len: Option<bool>) -> Result<()> {
            if write_len.is_none() || write_len.unwrap() {
                let bytes_len: u32 = value.len() as u32;
                self.write_u32(bytes_len)?;
            }
            self.inner.write_all(value)
        }

        build_write_array_fn!(write_bool_array, write_bool, bool);
        build_write_array_fn!(write_char_array, write_char, char);
        build_write_array_fn!(write_f16_array, write_f16, f32);
        build_write_array_fn!(write_cstr_array, write_cstr, &str);
        build_write_array_fn_arg!(write_str_array, write_str, &str);
        build_write_array_fn_arg!(write_bytes_array, write_bytes, &[u8]);
    };
}

macro_rules! build_write_fn_ve {
    ($type:ty) => {
        paste::item! {
            fn [< write_ $type >] (&mut self, value: $type) -> Result<()> {
                match self.endian {
                    Endian::Little => self.inner.write_all(&value.to_le_bytes()),
                    Endian::Big => self.inner.write_all(&value.to_be_bytes()),
                }
            }
        }
        paste::item! {
            fn [< write_ $type _array >] (&mut self, value: Vec<$type>, write_len: Option<bool>) -> Result<()> {
                if write_len.is_none() || write_len.unwrap() {
                    let array_len: u32 = value.len() as u32;
                    match self.endian {
                        Endian::Little => self.inner.write_all(&array_len.to_le_bytes())?,
                        Endian::Big => self.inner.write_all(&array_len.to_be_bytes())?,
                    };
                }
                // TODO - optimize this
                match self.endian {
                    Endian::Little => {
                        value.iter().for_each(|v| {
                            self.inner.write_all(&v.to_le_bytes()).unwrap();
                        });
                    }
                    Endian::Big => {
                        value.iter().for_each(|v| {
                            self.inner.write_all(&v.to_be_bytes()).unwrap();
                        });
                    }
                }
                Ok(())
            }
        }
    };
}

pub struct BinaryWriterVE<W> {
    inner: W,
    endian: Endian,
}

impl<W: Write> BinaryWriterVE<W> {
    pub fn new(inner: W, endian: Endian) -> Self {
        Self { inner, endian }
    }
}

impl<W: Write> BinaryWrite for BinaryWriterVE<W> {
    write_fn_generic!();
    build_write_fn_ve!(u8);
    build_write_fn_ve!(u16);
    build_write_fn_ve!(u32);
    build_write_fn_ve!(u64);

    build_write_fn_ve!(i8);
    build_write_fn_ve!(i16);
    build_write_fn_ve!(i32);
    build_write_fn_ve!(i64);
    build_write_fn_ve!(f32);
    build_write_fn_ve!(f64);
}

macro_rules! build_write_fn_be {
    ($type:ty) => {
        paste::item! {
            fn [< write_ $type >] (&mut self, value: $type) -> Result<()> {
                self.inner.write_all(&value.to_be_bytes())
            }
        }
        paste::item! {
            fn [< write_ $type _array >] (&mut self, value: Vec<$type>, write_len: Option<bool>) -> Result<()> {
                if write_len.is_none() || write_len.unwrap() {
                    self.write_u32(value.len() as u32)?;
                }
                // TODO - optimize this
                value.iter().for_each(|v| {
                    self.inner.write_all(&v.to_be_bytes()).unwrap();
                });
                Ok(())
            }
        }
    };
}
pub struct BinaryWriterBE<W> {
    inner: W,
}

impl<W: Write> BinaryWriterBE<W> {
    pub fn new(inner: W) -> Self {
        Self { inner }
    }
}

impl<W: Write> BinaryWrite for BinaryWriterBE<W> {
    write_fn_generic!();
    build_write_fn_be!(u8);
    build_write_fn_be!(u16);
    build_write_fn_be!(u32);
    build_write_fn_be!(u64);

    build_write_fn_be!(i8);
    build_write_fn_be!(i16);
    build_write_fn_be!(i32);
    build_write_fn_be!(i64);
    build_write_fn_be!(f32);
    build_write_fn_be!(f64);
}

macro_rules! build_write_fn_le {
    ($type:ty) => {
        paste::item! {
            fn [< write_ $type >] (&mut self, value: $type) -> Result<()> {
                self.inner.write_all(&value.to_le_bytes())
            }
        }
        paste::item! {
            fn [< write_ $type _array >] (&mut self, value: Vec<$type>, write_len: Option<bool>) -> Result<()> {
                if write_len.is_none() || write_len.unwrap() {
                    self.write_u32(value.len() as u32)?;
                }
                // TODO - optimize this
                value.iter().for_each(|v| {
                    self.inner.write_all(&v.to_le_bytes()).unwrap();
                });
                Ok(())
            }
        }
    };
}

pub struct BinaryWriterLE<W> {
    inner: W,
}

impl<W: Write> BinaryWriterLE<W> {
    pub fn new(inner: W) -> Self {
        Self { inner }
    }
}

impl<W: Write> BinaryWrite for BinaryWriterLE<W> {
    write_fn_generic!();
    build_write_fn_le!(u8);
    build_write_fn_le!(u16);
    build_write_fn_le!(u32);
    build_write_fn_le!(u64);

    build_write_fn_le!(i8);
    build_write_fn_le!(i16);
    build_write_fn_le!(i32);
    build_write_fn_le!(i64);
    build_write_fn_le!(f32);
    build_write_fn_le!(f64);
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

build_align_fn!(BinaryWriterLE);
build_align_fn!(BinaryWriterBE);
build_align_fn!(BinaryWriterVE);

#[cfg(test)]
mod tests {
    use super::*;
    fn write_unsigned(writer: &mut impl (BinaryWrite)) -> Result<()> {
        writer.write_u8(0x1 as u8)?;
        writer.write_u16(0x1234 as u16)?;
        writer.write_u32(0x12345678 as u32)?;
        writer.write_u64(0x1234567890123456 as u64)?;
        Ok(())
    }

    fn write_signed(writer: &mut dyn BinaryWrite) -> Result<()> {
        writer.write_i8(0x1 as i8)?;
        writer.write_i16(-0x1234 as i16)?;
        writer.write_i32(0x12345678 as i32)?;
        writer.write_i64(-0x1234567890123456 as i64)?;
        Ok(())
    }

    fn write_float(writer: &mut dyn BinaryWrite) -> Result<()> {
        writer.write_f16(0.16)?;
        writer.write_f32(-0.32)?;
        writer.write_f64(0.64)?;
        Ok(())
    }

    #[test]
    pub fn test_binary_writer() {
        let mut writer_vec = vec![];
        let mut writer = BinaryWriterVE::new(&mut writer_vec, Endian::Little);
        write_unsigned(&mut writer).unwrap();
        assert_eq!(writer_vec, &b"\x014\x12xV4\x12V4\x12\x90xV4\x12"[..]);

        let mut writer_vec = vec![];
        let mut writer = BinaryWriterVE::new(&mut writer_vec, Endian::Little);
        write_signed(&mut writer).unwrap();
        assert_eq!(
            writer_vec,
            &b"\x01\xcc\xedxV4\x12\xaa\xcb\xedo\x87\xa9\xcb\xed"[..]
        );

        let mut writer_vec = vec![];
        let mut writer = BinaryWriterVE::new(&mut writer_vec, Endian::Little);
        write_float(&mut writer).unwrap();
        assert_eq!(writer_vec, &b"\x1f1\n\xd7\xa3\xbe{\x14\xaeG\xe1z\xe4?"[..]);

        let mut writer_vec = vec![];
        let mut writer = BinaryWriterVE::new(&mut writer_vec, Endian::Big);
        write_unsigned(&mut writer).unwrap();
        assert_eq!(writer_vec, &b"\x01\x124\x124Vx\x124Vx\x90\x124V"[..]);

        let mut writer_vec = vec![];
        let mut writer = BinaryWriterVE::new(&mut writer_vec, Endian::Big);
        write_signed(&mut writer).unwrap();
        assert_eq!(
            writer_vec,
            &b"\x01\xed\xcc\x124Vx\xed\xcb\xa9\x87o\xed\xcb\xaa"[..]
        );

        let mut writer_vec = vec![];
        let mut writer = BinaryWriterVE::new(&mut writer_vec, Endian::Big);
        write_float(&mut writer).unwrap();
        assert_eq!(writer_vec, &b"1\x1f\xbe\xa3\xd7\n?\xe4z\xe1G\xae\x14{"[..]);
    }

    #[test]
    pub fn test_binary_writer_le() {
        let mut writer_vec = vec![];
        let mut writer = BinaryWriterLE::new(&mut writer_vec);
        write_unsigned(&mut writer).unwrap();
        assert_eq!(writer_vec, &b"\x014\x12xV4\x12V4\x12\x90xV4\x12"[..]);

        let mut writer_vec = vec![];
        let mut writer = BinaryWriterLE::new(&mut writer_vec);
        write_signed(&mut writer).unwrap();
        assert_eq!(
            writer_vec,
            &b"\x01\xcc\xedxV4\x12\xaa\xcb\xedo\x87\xa9\xcb\xed"[..]
        );

        let mut writer_vec = vec![];
        let mut writer = BinaryWriterLE::new(&mut writer_vec);
        write_float(&mut writer).unwrap();
        assert_eq!(writer_vec, &b"\x1f1\n\xd7\xa3\xbe{\x14\xaeG\xe1z\xe4?"[..]);
    }

    #[test]
    pub fn test_binary_writer_be() {
        let mut writer_vec = vec![];
        let mut writer = BinaryWriterBE::new(&mut writer_vec);
        write_unsigned(&mut writer).unwrap();
        assert_eq!(writer_vec, &b"\x01\x124\x124Vx\x124Vx\x90\x124V"[..]);

        let mut writer_vec = vec![];
        let mut writer = BinaryWriterBE::new(&mut writer_vec);
        write_signed(&mut writer).unwrap();
        assert_eq!(
            writer_vec,
            &b"\x01\xed\xcc\x124Vx\xed\xcb\xa9\x87o\xed\xcb\xaa"[..]
        );

        let mut writer_vec = vec![];
        let mut writer = BinaryWriterBE::new(&mut writer_vec);
        write_float(&mut writer).unwrap();
        assert_eq!(writer_vec, &b"1\x1f\xbe\xa3\xd7\n?\xe4z\xe1G\xae\x14{"[..]);
    }
}
