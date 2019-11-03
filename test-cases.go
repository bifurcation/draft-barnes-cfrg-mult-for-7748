package main

import (
	"bytes"
	"crypto/rand"
	"encoding/hex"
	"fmt"
	"math/big"

	"golang.org/x/crypto/curve25519"
)

var (
	prng     = rand.Reader
	n25519x  = "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
	p        *big.Int // Order of prime-order subgroup. (E.g n25519x for X25519)
	n        *big.Int // Order of composite-order group. n = p * cofactor
	cofactor *big.Int
)

func privToPub(a [32]byte) (aGx [32]byte) {
	curve25519.ScalarBaseMult(&aGx, &a)
	return
}

func newKeyPair() (a, aGx [32]byte) {
	prng.Read(a[:])
	aGx = privToPub(a)
	return
}

func keyPairFromHex(ax string) (a, aG [32]byte) {
	ab, _ := hex.DecodeString(ax)
	copy(a[:], ab)
	a = reverse(a)
	aG = privToPub(a)
	return
}

func dh(a, bGx [32]byte) (abGx [32]byte) {
	curve25519.ScalarMult(&abGx, &a, &bGx)
	return
}

func reverse(in [32]byte) (out [32]byte) {
	for i, x := range in {
		out[len(in)-i-1] = x
	}
	return
}

func le2bn(le [32]byte) *big.Int {
	be := reverse(le)
	return big.NewInt(0).SetBytes(be[:])
}

func bn2le(bn *big.Int) [32]byte {
	sl := bn.Bytes()
	pad := bytes.Repeat([]byte{0}, 32-len(sl))
	sl = append(pad, sl...)

	be := [32]byte{}
	copy(be[:], sl)
	return reverse(be)
}

func newDelta() (d [32]byte) {
	prng.Read(d[:])
	return
}

func clamp(a [32]byte) *big.Int {
	out := a
	out[0] &= 248
	out[31] &= 127
	out[31] |= 64
	return le2bn(out)
}

func log(label string, x [32]byte) {
	fmt.Printf("%-4s %064x\n", label, x)
}

func logn(label string, x *big.Int) {
	log(label, bn2le(x))
}

func cswap(c uint, a, b *big.Int) {
	if c == 1 {
		temp := *a
		*a = *b
		*b = temp
	}
}

func deltaPriv(d, sk [32]byte) [32]byte {
	dC := clamp(d)
	skC := clamp(sk)

	skP := big.NewInt(0)
	skP.Mul(dC, skC)
	skP.Mod(skP, n)

	skN := big.NewInt(0)
	skN.Sub(n, skP)

	cP := skP.Bit(254)

	logn("dC", dC)
	logn("skC", skC)
	logn("skP", skP)
	logn("skN", skN)
	logn("cP", big.NewInt(int64(cP)))

	cswap(1-cP, skP, skN)

	return bn2le(skP)
}

func deltaPub(d, aGx [32]byte) [32]byte {
	return dh(d, aGx)
}

func main() {
	/* X25519 Constants
	       ----------------
		   cofactor = 8
		   p        = n25519       = prime order
		   n        = p * cofactor = composite group order.
	*/
	p, _ = big.NewInt(0).SetString(n25519x, 16)
	cofactor = big.NewInt(8)
	n = big.NewInt(0)
	n.Mul(p, cofactor)

	sk0, pk0 := newKeyPair()
	d := newDelta()

	log("sk0", sk0)
	log("pk0", pk0)
	log("d", d)

	// Apply the delta
	sk1 := deltaPriv(d, sk0)
	pk1 := deltaPub(d, pk0)

	// Check if the homomorphism applies
	sk1p := privToPub(sk1)
	log("sk1", sk1)
	log("pk1", pk1)
	log("sk1p", sk1p)
}
