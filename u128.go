// Copyright 2021 github.com/gagliardetto
// This file has been modified by github.com/gagliardetto
//
// Copyright 2020 dfuse Platform Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package bin

import (
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"math/bits"
	"strings"
)

// Uint128
type Uint128 struct {
	Lo         uint64
	Hi         uint64
	Endianness binary.ByteOrder
}

func NewUint128BE() *Uint128 {
	return &Uint128{
		Endianness: binary.BigEndian,
	}
}

func NewUint128LE() *Uint128 {
	return &Uint128{
		Endianness: binary.LittleEndian,
	}
}

func NewUint128From64(x uint64, endianness ...binary.ByteOrder) Uint128 {
	r := Uint128{
		Lo: x,
		Hi: 0,
	}

	if len(endianness) == 1 {
		r.Endianness = endianness[0]
	}

	return r
}

func NewUint128LEFromBytes(b []byte) Uint128 {
	return Uint128{
		Lo:         binary.LittleEndian.Uint64(b[:8]),
		Hi:         binary.LittleEndian.Uint64(b[8:]),
		Endianness: binary.LittleEndian,
	}
}

func NewUint128BEFromBytes(b []byte) Uint128 {
	return Uint128{
		Lo:         binary.BigEndian.Uint64(b[8:]),
		Hi:         binary.BigEndian.Uint64(b[:8]),
		Endianness: binary.BigEndian,
	}
}

func (i Uint128) IsZero() bool {
	return i.Lo == 0 && i.Hi == 0
}

func (i Uint128) Equals(v Uint128) bool {
	return i.Lo == v.Lo && i.Hi == v.Hi
}

func (i Uint128) Equals64(v uint64) bool {
	return i.Lo == v && i.Hi == 0
}

func (i Uint128) Cmp(v Uint128) int {
	if i.Equals(v) {
		return 0
	} else if i.Hi < v.Hi || (i.Hi == v.Hi && i.Lo < v.Lo) {
		return -1
	} else {
		return 1
	}
}

func (i Uint128) Cmp64(v uint64) int {
	if i.Hi == 0 && i.Lo == v {
		return 0
	} else if i.Hi == 0 && i.Lo < v {
		return -1
	} else {
		return 1
	}
}

func (i Uint128) And(v Uint128) Uint128 {
	return Uint128{Lo: i.Lo & v.Lo, Hi: i.Hi & v.Hi}
}

func (i Uint128) And64(v uint64) Uint128 {
	return Uint128{Lo: i.Lo & v, Hi: i.Hi & 0}
}

func (i Uint128) Or(v Uint128) Uint128 {
	return Uint128{Lo: i.Lo | v.Lo, Hi: i.Hi | v.Hi}
}

func (u Uint128) Or64(v uint64) Uint128 {
	return Uint128{Lo: u.Lo | v, Hi: u.Hi | 0}
}

// Xor returns u^v.
func (i Uint128) Xor(v Uint128) Uint128 {
	return Uint128{Lo: i.Lo ^ v.Lo, Hi: i.Hi ^ v.Hi, Endianness: i.Endianness}
}

// Xor64 returns u^v.
func (i Uint128) Xor64(v uint64) Uint128 {
	return Uint128{Lo: i.Lo ^ v, Hi: i.Hi ^ 0, Endianness: i.Endianness}
}

// Add returns u+v.
func (i Uint128) Add(v Uint128) Uint128 {
	lo, carry := bits.Add64(i.Lo, v.Lo, 0)
	hi, carry := bits.Add64(i.Hi, v.Hi, carry)
	if carry != 0 {
		panic("overflow")
	}
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// AddWrap returns u+v with wraparound semantics.
func (i Uint128) AddWrap(v Uint128) Uint128 {
	lo, carry := bits.Add64(i.Lo, v.Lo, 0)
	hi, _ := bits.Add64(i.Hi, v.Hi, carry)
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// Add64 returns u+v.
func (i Uint128) Add64(v uint64) Uint128 {
	lo, carry := bits.Add64(i.Lo, v, 0)
	hi, carry := bits.Add64(i.Hi, 0, carry)
	if carry != 0 {
		panic("overflow")
	}
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// AddWrap64 returns u+v with wraparound semantics.
func (i Uint128) AddWrap64(v uint64) Uint128 {
	lo, carry := bits.Add64(i.Lo, v, 0)
	hi := i.Hi + carry
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// Sub returns u-v.
func (i Uint128) Sub(v Uint128) Uint128 {
	lo, borrow := bits.Sub64(i.Lo, v.Lo, 0)
	hi, borrow := bits.Sub64(i.Hi, v.Hi, borrow)
	if borrow != 0 {
		panic("underflow")
	}
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// SubWrap returns u-v with wraparound semantics.
func (i Uint128) SubWrap(v Uint128) Uint128 {
	lo, borrow := bits.Sub64(i.Lo, v.Lo, 0)
	hi, _ := bits.Sub64(i.Hi, v.Hi, borrow)
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// Sub64 returns u-v.
func (i Uint128) Sub64(v uint64) Uint128 {
	lo, borrow := bits.Sub64(i.Lo, v, 0)
	hi, borrow := bits.Sub64(i.Hi, 0, borrow)
	if borrow != 0 {
		panic("underflow")
	}
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// SubWrap64 returns u-v with wraparound semantics.
func (i Uint128) SubWrap64(v uint64) Uint128 {
	lo, borrow := bits.Sub64(i.Lo, v, 0)
	hi := i.Hi - borrow
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// Mul returns u*v, panicking on overflow.
func (i Uint128) Mul(v Uint128) Uint128 {
	hi, lo := bits.Mul64(i.Lo, v.Lo)
	p0, p1 := bits.Mul64(i.Hi, v.Lo)
	p2, p3 := bits.Mul64(i.Lo, v.Hi)
	hi, c0 := bits.Add64(hi, p1, 0)
	hi, c1 := bits.Add64(hi, p3, c0)
	if (i.Hi != 0 && v.Hi != 0) || p0 != 0 || p2 != 0 || c1 != 0 {
		panic("overflow")
	}
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// MulWrap returns u*v with wraparound semantics.
func (i Uint128) MulWrap(v Uint128) Uint128 {
	hi, lo := bits.Mul64(i.Lo, v.Lo)
	hi += i.Hi*v.Lo + i.Lo*v.Hi
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// Mul64 returns u*v, panicking on overflow.
func (i Uint128) Mul64(v uint64) Uint128 {
	hi, lo := bits.Mul64(i.Lo, v)
	p0, p1 := bits.Mul64(i.Hi, v)
	hi, c0 := bits.Add64(hi, p1, 0)
	if p0 != 0 || c0 != 0 {
		panic("overflow")
	}
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// MulWrap64 returns u*v with wraparound semantics.
func (i Uint128) MulWrap64(v uint64) Uint128 {
	hi, lo := bits.Mul64(i.Lo, v)
	hi += i.Hi * v
	return Uint128{Lo: lo, Hi: hi, Endianness: i.Endianness}
}

// Div returns u/v.
func (i Uint128) Div(v Uint128) Uint128 {
	q, _ := i.QuoRem(v)
	return q
}

// Div64 returns u/v.
func (i Uint128) Div64(v uint64) Uint128 {
	q, _ := i.QuoRem64(v)
	return q
}

// QuoRem returns q = u/v and r = u%v.
func (i Uint128) QuoRem(v Uint128) (q, r Uint128) {
	if v.Hi == 0 {
		var r64 uint64
		q, r64 = i.QuoRem64(v.Lo)
		r = NewUint128From64(r64, i.Endianness)
	} else {
		n := uint(bits.LeadingZeros64(v.Hi))
		v1 := v.Lsh(n)
		i1 := i.Rsh(1)
		tq, _ := bits.Div64(i1.Hi, i1.Lo, v1.Hi)
		tq >>= 63 - n
		if tq != 0 {
			tq--
		}
		q = NewUint128From64(tq, i.Endianness)
		r = i.Sub(v.Mul64(tq))
		if r.Cmp(v) >= 0 {
			q = q.Add64(1)
			r = r.Sub(v)
		}
	}
	return
}

// QuoRem64 returns q = u/v and r = u%v.
func (i Uint128) QuoRem64(v uint64) (q Uint128, r uint64) {
	if i.Hi < v {
		q.Lo, r = bits.Div64(i.Hi, i.Lo, v)
	} else {
		q.Hi, r = bits.Div64(0, i.Hi, v)
		q.Lo, r = bits.Div64(r, i.Lo, v)
	}
	return
}

// Mod returns r = u%v.
func (i Uint128) Mod(v Uint128) Uint128 {
	_, r := i.QuoRem(v)
	return r
}

// Mod64 returns r = u%v.
func (i Uint128) Mod64(v uint64) uint64 {
	_, r := i.QuoRem64(v)
	return r
}

// Lsh returns u<<n.
func (i Uint128) Lsh(n uint) Uint128 {
	if n > 64 {
		return Uint128{Lo: 0, Hi: i.Lo << (n - 64), Endianness: i.Endianness}
	}
	return Uint128{Lo: i.Lo << n, Hi: i.Hi<<n | i.Lo>>(64-n), Endianness: i.Endianness}
}

// Rsh returns u>>n.
func (i Uint128) Rsh(n uint) Uint128 {
	if n > 64 {
		return Uint128{Lo: i.Hi >> (n - 64), Hi: 0, Endianness: i.Endianness}
	}
	return Uint128{Lo: i.Lo>>n | i.Hi<<(64-n), Hi: i.Hi >> n, Endianness: i.Endianness}
}

// LeadingZeros returns the number of leading zero bits in u.
func (i Uint128) LeadingZeros() int {
	if i.Hi > 0 {
		return bits.LeadingZeros64(i.Hi)
	}
	return 64 + bits.LeadingZeros64(i.Lo)
}

// TrailingZeros returns the number of trailing zero bits in u.
func (i Uint128) TrailingZeros() int {
	if i.Lo > 0 {
		return bits.TrailingZeros64(i.Lo)
	}
	return 64 + bits.TrailingZeros64(i.Hi)
}

// OnesCount returns the number of one bits in u.
func (i Uint128) OnesCount() int {
	return bits.OnesCount64(i.Hi) + bits.OnesCount64(i.Lo)
}

// RotateLeft returns u rotated left by (k mod 128) bits.
func (i Uint128) RotateLeft(k int) Uint128 {
	const n = 128
	s := uint(k) & (n - 1)
	return i.Lsh(s).Or(i.Rsh(n - s))
}

// RotateRight returns u rotated right by (k mod 128) bits.
func (i Uint128) RotateRight(k int) Uint128 {
	return i.RotateLeft(-k)
}

func (i Uint128) getByteOrder() binary.ByteOrder {
	if i.Endianness == nil {
		return defaultByteOrder
	}
	return i.Endianness
}

func (i Int128) getByteOrder() binary.ByteOrder {
	return Uint128(i).getByteOrder()
}
func (i Float128) getByteOrder() binary.ByteOrder {
	return Uint128(i).getByteOrder()
}

func (i Uint128) Bytes() []byte {
	buf := make([]byte, 16)
	order := i.getByteOrder()
	if order == binary.LittleEndian {
		order.PutUint64(buf[:8], i.Lo)
		order.PutUint64(buf[8:], i.Hi)
		ReverseBytes(buf)
	} else {
		order.PutUint64(buf[:8], i.Hi)
		order.PutUint64(buf[8:], i.Lo)
	}
	return buf
}

func (i Uint128) BigInt() *big.Int {
	buf := i.Bytes()
	value := (&big.Int{}).SetBytes(buf)
	return value
}

func (i Uint128) String() string {
	//Same for Int128, Float128
	return i.DecimalString()
}

func (i Uint128) DecimalString() string {
	return i.BigInt().String()
}

func (i Uint128) HexString() string {
	number := i.Bytes()
	return fmt.Sprintf("0x%s", hex.EncodeToString(number))
}

func (i Uint128) MarshalJSON() (data []byte, err error) {
	return []byte(`"` + i.String() + `"`), nil
}

func ReverseBytes(s []byte) {
	for i, j := 0, len(s)-1; i < j; i, j = i+1, j-1 {
		s[i], s[j] = s[j], s[i]
	}
}

func (i *Uint128) UnmarshalJSON(data []byte) error {
	if string(data) == "null" {
		return nil
	}

	var s string
	if err := json.Unmarshal(data, &s); err != nil {
		return err
	}

	if strings.HasPrefix(s, "0x") || strings.HasPrefix(s, "0X") {
		return i.unmarshalJSON_hex(s)
	}

	return i.unmarshalJSON_decimal(s)
}

func (i *Uint128) unmarshalJSON_decimal(s string) error {
	parsed, ok := (&big.Int{}).SetString(s, 0)
	if !ok {
		return fmt.Errorf("could not parse %q", s)
	}
	oo := parsed.FillBytes(make([]byte, 16))
	ReverseBytes(oo)

	dec := NewBinDecoder(oo)

	out, err := dec.ReadUint128(i.getByteOrder())
	if err != nil {
		return err
	}
	i.Lo = out.Lo
	i.Hi = out.Hi

	return nil
}

func (i *Uint128) unmarshalJSON_hex(s string) error {
	truncatedVal := s[2:]
	if len(truncatedVal) != 16 {
		return fmt.Errorf("uint128 expects 16 characters after 0x, had %v", len(truncatedVal))
	}

	data, err := hex.DecodeString(truncatedVal)
	if err != nil {
		return err
	}

	order := i.getByteOrder()
	if order == binary.LittleEndian {
		i.Lo = order.Uint64(data[:8])
		i.Hi = order.Uint64(data[8:])
	} else {
		i.Hi = order.Uint64(data[:8])
		i.Lo = order.Uint64(data[8:])
	}

	return nil
}

func (i *Uint128) UnmarshalWithDecoder(dec *Decoder) error {
	var order binary.ByteOrder
	if dec != nil && dec.currentFieldOpt != nil {
		order = dec.currentFieldOpt.Order
	} else {
		order = i.getByteOrder()
	}
	value, err := dec.ReadUint128(order)
	if err != nil {
		return err
	}

	*i = value
	return nil
}

func (i Uint128) MarshalWithEncoder(enc *Encoder) error {
	var order binary.ByteOrder
	if enc != nil && enc.currentFieldOpt != nil {
		order = enc.currentFieldOpt.Order
	} else {
		order = i.getByteOrder()
	}
	return enc.WriteUint128(i, order)
}

// Int128
type Int128 Uint128

func (i Int128) BigInt() *big.Int {
	comp := byte(0x80)
	buf := Uint128(i).Bytes()

	var value *big.Int
	if (buf[0] & comp) == comp {
		buf = twosComplement(buf)
		value = (&big.Int{}).SetBytes(buf)
		value = value.Neg(value)
	} else {
		value = (&big.Int{}).SetBytes(buf)
	}
	return value
}

func (i Int128) String() string {
	return Uint128(i).String()
}

func (i Int128) DecimalString() string {
	return i.BigInt().String()
}

func (i Int128) MarshalJSON() (data []byte, err error) {
	return []byte(`"` + Uint128(i).String() + `"`), nil
}

func (i *Int128) UnmarshalJSON(data []byte) error {
	var el Uint128
	if err := json.Unmarshal(data, &el); err != nil {
		return err
	}

	out := Int128(el)
	*i = out

	return nil
}

func (i *Int128) UnmarshalWithDecoder(dec *Decoder) error {
	var order binary.ByteOrder
	if dec != nil && dec.currentFieldOpt != nil {
		order = dec.currentFieldOpt.Order
	} else {
		order = i.getByteOrder()
	}
	value, err := dec.ReadInt128(order)
	if err != nil {
		return err
	}

	*i = value
	return nil
}

func (i Int128) MarshalWithEncoder(enc *Encoder) error {
	var order binary.ByteOrder
	if enc != nil && enc.currentFieldOpt != nil {
		order = enc.currentFieldOpt.Order
	} else {
		order = i.getByteOrder()
	}
	return enc.WriteInt128(i, order)
}

type Float128 Uint128

func (i Float128) MarshalJSON() (data []byte, err error) {
	return []byte(`"` + Uint128(i).String() + `"`), nil
}

func (i *Float128) UnmarshalJSON(data []byte) error {
	var el Uint128
	if err := json.Unmarshal(data, &el); err != nil {
		return err
	}

	out := Float128(el)
	*i = out

	return nil
}

func (i *Float128) UnmarshalWithDecoder(dec *Decoder) error {
	var order binary.ByteOrder
	if dec != nil && dec.currentFieldOpt != nil {
		order = dec.currentFieldOpt.Order
	} else {
		order = i.getByteOrder()
	}
	value, err := dec.ReadFloat128(order)
	if err != nil {
		return err
	}

	*i = Float128(value)
	return nil
}

func (i Float128) MarshalWithEncoder(enc *Encoder) error {
	var order binary.ByteOrder
	if enc != nil && enc.currentFieldOpt != nil {
		order = enc.currentFieldOpt.Order
	} else {
		order = i.getByteOrder()
	}
	return enc.WriteUint128(Uint128(i), order)
}
