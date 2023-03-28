//! A crate that implements endianed BinaryReaders for use in urex.
//!
//! This crate provides the [`BinaryReader`] and [`BinaryWriter`] traits and three implementations of them each,
//! 
//! The [`BinaryReader`] and [`BinaryWriter`] traits aren't implemented for `Read` and `Write` respectively, because
//! they are not endian aware. Instead, they are implemented for the three endian aware structs that either set the endianness or make it variable. 
//! The implementations are namely:
//! - [`BinaryReaderVE`], [`BinaryReaderLE`], [`BinaryReaderBE`]
//! - [`BinaryWriterVE`], [`BinaryWriterLE`], [`BinaryWriterBE`].
//! 
//! The `VE` stands for variable endian, the `LE` stands for little-endian, and the `BE` stands for big-endian.
//! The [`BinaryReaderVE`] and [`BinaryWriterVE`] structs are flexible, allowing you to set and change the endianness at runtime.
//! The endianness can be set by setting the `endian` field, which is of type [`Endian`].
//! The [`BinaryReaderLE`] and [`BinaryWriterLE`] structs are restrictive, as they only allow you to read/write little-endian data.
//! The [`BinaryReaderBE`] and [`BinaryWriterBE`] structs are restrictive, as they only allow you to read/write big-endian data.

mod reader;
mod writer;

pub use reader::{BinaryReader, BinaryReaderBE, BinaryReaderLE, BinaryReaderVE};
pub use writer::{BinaryWriter, BinaryWriterBE, BinaryWriterLE, BinaryWriterVE};

pub enum Endian {
    Little,
    Big,
}