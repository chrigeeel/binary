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
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/big"
	"math/bits"
	"strings"
)

// Uint128
type Uint128 [2]uint64

func NewUint128() *Uint128 {
	return &Uint128{}
}

func NewUint128From64(x uint64) *Uint128 {
	z := &Uint128{}
	z[1], z[0] = 0, x

	return z
}

func NewUint128FromBig(x *big.Int) *Uint128 {
	z := &Uint128{}

	z[0] = x.Uint64()
	z[1] = x.Rsh(x, 64).Uint64()

	return z
}

func (z *Uint128) Uint64() uint64 {
	return z[0]
}

func (z *Uint128) Clone() *Uint128 {
	return &Uint128{z[0], z[1]}
}

func (z *Uint128) Add(x, y *Uint128) *Uint128 {
	var carry uint64
	z[0], carry = bits.Add64(x[0], y[0], 0)
	z[1], _ = bits.Add64(x[1], y[1], carry)
	return z
}

func (z *Uint128) Add64(x *Uint128, y uint64) *Uint128 {
	var carry uint64
	z[0], carry = bits.Add64(x[0], y, 0)
	z[1], _ = bits.Add64(x[1], 0, carry)
	return z
}

func (z *Uint128) Sub(x, y *Uint128) *Uint128 {
	var carry uint64
	z[0], carry = bits.Sub64(x[0], y[0], 0)
	z[1], _ = bits.Sub64(x[1], y[1], carry)
	return z
}

func (z *Uint128) Sub64(x *Uint128, y uint64) *Uint128 {
	var carry uint64
	z[0], carry = bits.Sub64(x[0], y, 0)
	z[1], _ = bits.Sub64(x[1], 0, carry)
	return z
}

func (z *Uint128) Mul(x, y *Uint128) *Uint128 {
	var (
		p1, p3 uint64
		c0     uint64
		hi, lo uint64
	)

	hi, lo = bits.Mul64(x[0], y[0])
	_, p1 = bits.Mul64(x[1], y[0])
	_, p3 = bits.Mul64(x[0], y[1])
	hi, c0 = bits.Add64(hi, p1, 0)
	hi, _ = bits.Add64(hi, p3, c0)

	z[0], z[1] = lo, hi
	return z
}

func (z *Uint128) Mul64(x *Uint128, y uint64) *Uint128 {
	var (
		p1     uint64
		hi, lo uint64
	)

	hi, lo = bits.Mul64(x[0], y)
	_, p1 = bits.Mul64(x[1], y)
	hi, _ = bits.Add64(hi, p1, 0)

	z[0], z[1] = lo, hi
	return z
}

// Div returns u/v.
func (z *Uint128) Div(x, v *Uint128) *Uint128 {
	q, _ := QuoRem(x, v)
	z[0], z[1] = q[0], q[1]
	return z
}

// Div64 returns u/v.
func (z *Uint128) Div64(x *Uint128, v uint64) *Uint128 {
	q, _ := QuoRem64(x, v)
	z[0], z[1] = q[0], q[1]
	return z
}

func (z *Uint128) Mod(x, y *Uint128) *Uint128 {
	_, r := QuoRem(x, y)
	z[0], z[1] = r[0], r[1]
	return z
}

func (z *Uint128) Mod64(x *Uint128, y uint64) *Uint128 {
	_, r := QuoRem64(x, y)
	z[0], z[1] = r, 0
	return z
}

func QuoRem(x, y *Uint128) (*Uint128, *Uint128) {
	if y[1] == 0 {
		q, r64 := QuoRem64(x, y[0])
		return q, NewUint128From64(r64)
	} else {
		n := uint(bits.LeadingZeros64(y[1]))
		y1 := new(Uint128).Lsh(y, n)
		x1 := new(Uint128).Rsh(x, 1)
		tq, _ := bits.Div64(x1[1], x1[0], y1[1])
		tq >>= 63 - n
		if tq != 0 {
			tq--
		}
		q := NewUint128From64(tq)
		r := new(Uint128).Sub(x, new(Uint128).Mul64(y, tq))
		if r.Cmp(y) >= 0 {
			q.Add64(q, 1)
			r.Sub(r, y)
		}
		return q, r
	}
}

func QuoRem64(x *Uint128, y uint64) (*Uint128, uint64) {
	q := new(Uint128)
	var r uint64
	if x[1] < y {
		q[0], r = bits.Div64(x[1], x[0], y)
	} else {
		q[1], r = bits.Div64(0, x[1], y)
		q[0], r = bits.Div64(r, x[0], y)
	}
	return q, r
}

func (z *Uint128) Lsh(x *Uint128, n uint) *Uint128 {
	if n > 64 {
		z[0], z[1] = 0, x[0]<<(n-64)
	} else {
		z[0], z[1] = x[0]<<n, x[1]<<n|x[0]>>(64-n)
	}
	return z
}

func (z *Uint128) Rsh(x *Uint128, n uint) *Uint128 {
	if n > 64 {
		z[0], z[1] = x[1]>>(n-64), 0
	} else {
		z[0], z[1] = x[0]>>n|x[1]<<(64-n), x[1]>>n
	}
	return z
}

func (z *Uint128) LeadingZeros() int {
	if z[1] > 0 {
		return bits.LeadingZeros64(z[1])
	}
	return 64 + bits.LeadingZeros64(z[0])
}

func (z *Uint128) IsZero() bool {
	return z[0] == 0 && z[1] == 0
}

func (z *Uint128) Equals(x *Uint128) bool {
	return z[0] == x[0] && z[1] == x[1]
}

func (z *Uint128) Equals64(x uint64) bool {
	return z[0] == x && z[1] == 0
}

func (z *Uint128) Cmp(x *Uint128) int {
	if z.Equals(x) {
		return 0
	} else if z[1] < x[1] || (z[1] == x[1] && z[0] < x[0]) {
		return -1
	} else {
		return 1
	}
}

func (z *Uint128) Cmp64(x uint64) int {
	if z[1] == 0 && z[0] == x {
		return 0
	} else if z[1] == 0 && z[0] < x {
		return -1
	} else {
		return 1
	}
}

func (z *Uint128) And(x, y *Uint128) *Uint128 {
	z[0], z[1] = x[0]&y[0], x[1]&y[1]
	return z
}

func (z *Uint128) And64(x *Uint128, y uint64) *Uint128 {
	z[0], z[1] = x[0]&y, x[1]&0
	return z
}

func (z *Uint128) Or(x, y *Uint128) *Uint128 {
	z[0], z[1] = x[0]|y[0], x[1]|y[1]
	return z
}

func (z *Uint128) Or64(x *Uint128, y uint64) *Uint128 {
	z[0], z[1] = x[0]|y, x[1]|0
	return z
}

// Xor returns u^v.
func (z *Uint128) Xor(x, y *Uint128) *Uint128 {
	z[0], z[1] = x[0]^y[0], x[1]^y[1]
	return z
}

// Xor64 returns u^v.
func (z *Uint128) Xor64(x *Uint128, y uint64) *Uint128 {
	z[0], z[1] = x[0]^y, x[1]^0
	return z
}

func (z *Uint128) Bytes() []byte {
	buf := make([]byte, 16)
	LE.PutUint64(buf[:8], z[0])
	LE.PutUint64(buf[8:], z[1])
	ReverseBytes(buf)
	return buf
}

func (z *Uint128) BigInt() *big.Int {
	return new(big.Int).SetBytes(z.Bytes())
}

func (z *Uint128) String() string {
	//Same for Int128, Float128
	return z.DecimalString()
}

func (z *Uint128) DecimalString() string {
	return z.BigInt().String()
}

func (z *Uint128) HexString() string {
	return fmt.Sprintf("0x%s", hex.EncodeToString(z.Bytes()))
}

func (z Uint128) MarshalJSON() (data []byte, err error) {
	return []byte(`"` + z.String() + `"`), nil
}

func ReverseBytes(s []byte) {
	for i, j := 0, len(s)-1; i < j; i, j = i+1, j-1 {
		s[i], s[j] = s[j], s[i]
	}
}

func (z *Uint128) UnmarshalJSON(data []byte) error {
	if string(data) == "null" {
		return nil
	}

	var s string
	if err := json.Unmarshal(data, &s); err != nil {
		return err
	}

	if strings.HasPrefix(s, "0x") || strings.HasPrefix(s, "0X") {
		return z.unmarshalJSON_hex(s)
	}

	return z.unmarshalJSON_decimal(s)
}

func (z *Uint128) unmarshalJSON_decimal(s string) error {
	parsed, ok := new(big.Int).SetString(s, 0)
	if !ok {
		return fmt.Errorf("could not parse %q", s)
	}
	oo := parsed.FillBytes(make([]byte, 16))
	ReverseBytes(oo)

	dec := NewBinDecoder(oo)

	out, err := dec.ReadUint128()
	if err != nil {
		return err
	}
	z[0] = out[0]
	z[1] = out[1]

	return nil
}

func (z *Uint128) unmarshalJSON_hex(s string) error {
	truncatedVal := s[2:]
	if len(truncatedVal) != 16 {
		return fmt.Errorf("uint128 expects 16 characters after 0x, had %v", len(truncatedVal))
	}

	data, err := hex.DecodeString(truncatedVal)
	if err != nil {
		return err
	}

	z[0] = LE.Uint64(data[:8])
	z[1] = LE.Uint64(data[8:])

	return nil
}

func (z *Uint128) UnmarshalWithDecoder(dec *Decoder) error {
	value, err := dec.ReadUint128()
	if err != nil {
		return err
	}

	*z = value
	return nil
}

func (z Uint128) MarshalWithEncoder(enc *Encoder) error {
	return enc.WriteUint128(z)
}
