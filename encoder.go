package bin

import (
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"math"
	"reflect"

	"go.uber.org/zap"
)

type Encoder struct {
	output io.Writer
	count  int

	currentFieldOpt *option

	encoding Encoding
}

func (enc *Encoder) IsBorsh() bool {
	return enc.encoding.IsBorsh()
}

func (enc *Encoder) IsBin() bool {
	return enc.encoding.IsBin()
}

func (enc *Encoder) IsCompactU16() bool {
	return enc.encoding.IsCompactU16()
}

func NewEncoderWithEncoding(writer io.Writer, enc Encoding) *Encoder {
	if !isValidEncoding(enc) {
		panic(fmt.Sprintf("provided encoding is not valid: %s", enc))
	}
	return &Encoder{
		output:   writer,
		count:    0,
		encoding: enc,
	}
}

func NewBinEncoder(writer io.Writer) *Encoder {
	return NewEncoderWithEncoding(writer, EncodingBin)
}

func NewBorshEncoder(writer io.Writer) *Encoder {
	return NewEncoderWithEncoding(writer, EncodingBorsh)
}

func NewCompactU16Encoder(writer io.Writer) *Encoder {
	return NewEncoderWithEncoding(writer, EncodingCompactU16)
}

func (e *Encoder) Encode(v interface{}) (err error) {
	switch e.encoding {
	case EncodingBin:
		return e.encodeBin(reflect.ValueOf(v), nil)
	case EncodingBorsh:
		return e.encodeBorsh(reflect.ValueOf(v), nil)
	case EncodingCompactU16:
		return e.encodeCompactU16(reflect.ValueOf(v), nil)
	default:
		panic(fmt.Errorf("encoding not implemented: %s", e.encoding))
	}
}

func (e *Encoder) toWriter(bytes []byte) (err error) {
	e.count += len(bytes)

	if traceEnabled {
		zlog.Debug("	> encode: appending", zap.Stringer("hex", HexBytes(bytes)), zap.Int("pos", e.count))
	}

	_, err = e.output.Write(bytes)
	return
}

func (e *Encoder) WriteBytes(b []byte, writeLength bool) error {
	if traceEnabled {
		zlog.Debug("encode: write byte array", zap.Int("len", len(b)))
	}
	if writeLength {
		switch e.encoding {
		case EncodingBin:
			if err := e.WriteUVarInt(len(b)); err != nil {
				return err
			}
		case EncodingBorsh:
			if err := e.WriteUint32(uint32(len(b)), LE()); err != nil {
				return err
			}
		case EncodingCompactU16:
			var buf []byte
			EncodeCompactU16Length(&buf, len(b))
			if err := e.WriteBytes(buf, false); err != nil {
				return err
			}
		default:
			panic(fmt.Errorf("encoding not implemented: %s", e.encoding))
		}
	}
	if len(b) == 0 {
		return nil
	}
	return e.toWriter(b)
}

func (e *Encoder) WriteUVarInt(v int) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write uvarint", zap.Int("val", v))
	}

	buf := make([]byte, 8)
	l := binary.PutUvarint(buf, uint64(v))
	return e.toWriter(buf[:l])
}

func (e *Encoder) WriteVarInt(v int) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write varint", zap.Int("val", v))
	}

	buf := make([]byte, 8)
	l := binary.PutVarint(buf, int64(v))
	return e.toWriter(buf[:l])
}

func (e *Encoder) WriteByte(b byte) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write byte", zap.Uint8("val", b))
	}
	return e.toWriter([]byte{b})
}

func (e *Encoder) WriteBool(b bool) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write bool", zap.Bool("val", b))
	}
	var out byte
	if b {
		out = 1
	}
	return e.WriteByte(out)
}

func (e *Encoder) WriteUint8(i uint8) (err error) {
	return e.WriteByte(i)
}

func (e *Encoder) WriteUint16(i uint16, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write uint16", zap.Uint16("val", i))
	}
	buf := make([]byte, TypeSize.Uint16)
	order.PutUint16(buf, i)
	return e.toWriter(buf)
}

func (e *Encoder) WriteInt16(i int16, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write int16", zap.Int16("val", i))
	}
	return e.WriteUint16(uint16(i), order)
}

func (e *Encoder) WriteInt32(i int32, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write int32", zap.Int32("val", i))
	}
	return e.WriteUint32(uint32(i), order)
}

func (e *Encoder) WriteUint32(i uint32, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write uint32", zap.Uint32("val", i))
	}
	buf := make([]byte, TypeSize.Uint32)
	order.PutUint32(buf, i)
	return e.toWriter(buf)
}

func (e *Encoder) WriteInt64(i int64, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write int64", zap.Int64("val", i))
	}
	return e.WriteUint64(uint64(i), order)
}

func (e *Encoder) WriteUint64(i uint64, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write uint64", zap.Uint64("val", i))
	}
	buf := make([]byte, TypeSize.Uint64)
	order.PutUint64(buf, i)
	return e.toWriter(buf)
}

func (e *Encoder) WriteUint128(i Uint128, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write uint128", zap.Stringer("hex", i), zap.Uint64("lo", i.Lo), zap.Uint64("hi", i.Hi))
	}
	buf := make([]byte, TypeSize.Uint128)
	order.PutUint64(buf, i.Lo)
	order.PutUint64(buf[TypeSize.Uint64:], i.Hi)
	return e.toWriter(buf)
}

func (e *Encoder) WriteInt128(i Int128, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write int128", zap.Stringer("hex", i), zap.Uint64("lo", i.Lo), zap.Uint64("hi", i.Hi))
	}
	buf := make([]byte, TypeSize.Uint128)
	order.PutUint64(buf, i.Lo)
	order.PutUint64(buf[TypeSize.Uint64:], i.Hi)
	return e.toWriter(buf)
}

func (e *Encoder) WriteFloat32(f float32, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write float32", zap.Float32("val", f))
	}

	if e.IsBorsh() {
		if float64(f) == math.NaN() {
			return errors.New("NaN float value")
		}
	}

	i := math.Float32bits(f)
	buf := make([]byte, TypeSize.Uint32)
	order.PutUint32(buf, i)

	return e.toWriter(buf)
}
func (e *Encoder) WriteFloat64(f float64, order binary.ByteOrder) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write float64", zap.Float64("val", f))
	}

	if e.IsBorsh() {
		if float64(f) == math.NaN() {
			return errors.New("NaN float value")
		}
	}
	i := math.Float64bits(f)
	buf := make([]byte, TypeSize.Uint64)
	order.PutUint64(buf, i)

	return e.toWriter(buf)
}

func (e *Encoder) WriteString(s string) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write string", zap.String("val", s))
	}
	return e.WriteBytes([]byte(s), true)
}

func (e *Encoder) WriteCompactU16Length(ln int) (err error) {
	if traceEnabled {
		zlog.Debug("encode: write compact-u16 length", zap.Int("val", ln))
	}
	buf := make([]byte, 0)
	EncodeCompactU16Length(&buf, ln)
	return e.toWriter(buf)
}

// TODO: add rust string.
// https://github.com/bmresearch/Solnet/blob/7826cc93ec6c997fc997a7a3c6be0f3511ca0c63/src/Solnet.Programs/Utilities/Serialization.cs#L219
// public static byte[] EncodeRustString(string data)
// {
//     byte[] stringBytes = Encoding.ASCII.GetBytes(data);
//     byte[] encoded = new byte[stringBytes.Length + sizeof(uint)];

//     encoded.WriteU32((uint) stringBytes.Length, 0);
//     encoded.WriteSpan(stringBytes, sizeof(uint));
//     return encoded;
// }
