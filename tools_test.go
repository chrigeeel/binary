package bin

func concatByteSlices(slices ...[]byte) (out []byte) {
	for i := range slices {
		out = append(out, slices[i]...)
	}
	return
}
func uint16ToBytes(i uint16) []byte {
	buf := make([]byte, 2)
	LE.PutUint16(buf, i)
	return buf
}

func uint32ToBytes(i uint32) []byte {
	buf := make([]byte, 4)
	LE.PutUint32(buf, i)
	return buf
}

func uint64ToBytes(i uint64) []byte {
	buf := make([]byte, 8)
	LE.PutUint64(buf, i)
	return buf
}
