package main

import (
	"bytes"
	"fmt"
	"math/big"
	"math/rand"
	"time"

	curve448 "git.schwanenlied.me/yawning/x448.git"
	"golang.org/x/crypto/curve25519"
)

// XXX not constant time
func cswap(test uint, a, b *big.Int) {
	if test == 1 {
		temp := *a
		*a = *b
		*b = temp
	}
}

type Group struct {
	p  *big.Int // Prime subgroup order
	b  int      // Index of clamped bit
	h  *big.Int // Cofactor
	h2 *big.Int // Cofactor squared
	n  *big.Int
	m  *big.Int
}

func NewGroup(p *big.Int, b int, h int64) *Group {
	g := &Group{p: p, b: b, h: big.NewInt(h)}

	g.h2 = big.NewInt(0).Mul(g.h, g.h)
	g.n = big.NewInt(0).Mul(g.p, g.h)

	g.m = big.NewInt(1)
	g.m.Lsh(g.m, uint(b))
	g.m.Sub(g.m, big.NewInt(1))
	g.m.Sub(g.m, big.NewInt(0).Mod(g.m, g.h))

	return g
}

func (g Group) Clamp(x *big.Int) *big.Int {
	xc := big.NewInt(0).Set(x)
	xc.And(xc, g.m).SetBit(xc, g.b, 1)
	return xc
}

func (g Group) Clamped(x *big.Int) bool {
	return x.Cmp(g.Clamp(x)) == 0
}

func (g Group) Fail(x *big.Int) bool {
	return !g.Clamped(x) && !g.Clamped(big.NewInt(0).Sub(g.n, x))
}

type multState struct {
	dC  *big.Int
	skC *big.Int
	skP *big.Int
	skN *big.Int
	cP  uint
}

func (g Group) Mult(d, sk *big.Int) (*big.Int, *multState) {
	s := &multState{}
	s.dC = g.Clamp(d)
	s.skC = g.Clamp(sk)

	s.skP = big.NewInt(0).Mul(s.dC, s.skC)
	s.skP.Mod(s.skP, g.n)

	s.skN = big.NewInt(0).Sub(g.n, s.skP)

	s.cP = s.skP.Bit(g.b)
	cswap(1-s.cP, s.skP, s.skN)
	return s.skP, s
}

func (g Group) BadDelta(sk, lb, ub *big.Int) *big.Int {
	skC := g.Clamp(sk)

	ski := big.NewInt(0)
	gcd := big.NewInt(0)
	gcd.GCD(ski, nil, skC, g.n)
	if gcd.Cmp(g.h) != 0 {
		panic("Unexpected GCD")
	}

	// Target is first multiple of cofactor squared above lower bound.  This
	// ensures that the low-order bits of the delta are clamped.
	// TODO: use big.Rand(prng, ub - lb) + lb
	// t = lb + h2 - (lb % h2)
	t := big.NewInt(0).Add(lb, g.h2)
	t.Sub(t, big.NewInt(0).Mod(lb, g.h2))

	//          ai * a = h     (mod n)
	// => (c * ai) * a = c * h (mod n)
	//                 = t     (mod n)
	c := big.NewInt(0).Div(t, g.h)
	d := big.NewInt(0).Mul(c, ski)
	d.Mod(d, g.n)

	// n - d should also suffice
	e := big.NewInt(0).Sub(g.n, d)

	switch {
	case g.Clamped(d):
		return d
	case g.Clamped(e):
		return e
	default:
		panic("Rare failure")
	}
}

//////////

var (
	x25519x         = "14def9dea2f79cd65812631a5cf5d3ed"
	x25519, _       = big.NewInt(0).SetString(x25519x, 16)
	b25519    int   = 254
	h25519    int64 = 8

	x448x         = "8335dC163bb124b65129c96fde933d8d723a70aadC873d6d54a7bb0d"
	x448, _       = big.NewInt(0).SetString(x448x, 16)
	b448    int   = 447
	h448    int64 = 4

	g25519 *Group
	g448   *Group

	prng = rand.New(rand.NewSource(time.Now().Unix()))
)

func setup() {
	p25519 := big.NewInt(1)
	p25519.Lsh(p25519, 252)
	p25519.Add(p25519, x25519)
	g25519 = NewGroup(p25519, b25519, h25519)

	p448 := big.NewInt(1)
	p448.Lsh(p448, 446)
	p448.Sub(p448, x448)
	g448 = NewGroup(p448, b448, h448)
}

func random(lb, ub *big.Int) *big.Int {
	span := big.NewInt(0).Sub(ub, lb)
	val := big.NewInt(0).Rand(prng, span)
	val.Add(val, lb)
	return val
}

func reverse(in []byte) []byte {
	out := make([]byte, len(in))
	for i := len(in)/2 - 1; i >= 0; i-- {
		opp := len(in) - 1 - i
		out[i], out[opp] = in[opp], in[i]
	}
	return out
}

func bn32le(bn *big.Int) [32]byte {
	out := [32]byte{}
	copy(out[:], reverse(bn.Bytes()))
	return out
}

func bn56le(bn *big.Int) [56]byte {
	out := [56]byte{}
	copy(out[:], reverse(bn.Bytes()))
	return out
}

func bn2le(bn *big.Int, size int) []byte {
	le := reverse(bn.Bytes())
	pad := bytes.Repeat([]byte{0}, size-len(le))
	return append(le, pad...)
}

func printTestCase25519(label string, sk0, d *big.Int) {
	size := 32

	sk1, s := g25519.Mult(d, sk0)

	sk0x := bn32le(sk0)
	sk1x := bn32le(sk1)

	var pk0, pk1 [32]byte
	curve25519.ScalarBaseMult(&pk0, &sk0x)
	curve25519.ScalarBaseMult(&pk1, &sk1x)

	fmt.Printf("~~~ 25519 %s ~~~\n", label)
	fmt.Printf("sk0 %x\n", bn2le(sk0, size))
	fmt.Printf("pk0 %x\n", pk0)
	fmt.Printf("d   %x\n", bn2le(d, size))
	fmt.Printf("dC  %x\n", bn2le(s.dC, size))
	fmt.Printf("skC %x\n", bn2le(s.skC, size))
	fmt.Printf("skP %x\n", bn2le(s.skP, size))
	fmt.Printf("skN %x\n", bn2le(s.skN, size))
	fmt.Printf("cP  %d\n", s.cP)
	fmt.Printf("sk1 %x\n", bn2le(sk1, size))
	fmt.Printf("pk1 %x\n", pk1)
	fmt.Printf("\n")
}

func printTestCase448(label string, sk0, d *big.Int) {
	size := 56

	sk1, s := g448.Mult(d, sk0)

	sk0x := bn56le(sk0)
	sk1x := bn56le(sk1)

	var pk0, pk1 [56]byte
	curve448.ScalarBaseMult(&pk0, &sk0x)
	curve448.ScalarBaseMult(&pk1, &sk1x)

	print56 := func(label string, val []byte) {
		fmt.Printf("%-3s %x\n    %x\n", label, val[:28], val[28:])
	}

	fmt.Printf("~~~ 448 %s ~~~\n", label)
	print56("sk0", bn2le(sk0, size))
	print56("pk0", pk0[:])
	print56("d", bn2le(d, size))
	print56("dC", bn2le(s.dC, size))
	print56("skC", bn2le(s.skC, size))
	print56("skP", bn2le(s.skP, size))
	print56("skN", bn2le(s.skN, size))
	fmt.Printf("cP  %d\n", s.cP)
	print56("sk1", bn2le(sk1, size))
	print56("pk1", pk1[:])
	fmt.Printf("\n")
}

func check25519() {
	g := g25519

	// Check that homomorphism holds
	a := random(big.NewInt(0), g.n)
	d := random(big.NewInt(0), g.n)
	da, _ := g.Mult(d, a)

	ax := bn32le(a)
	dx := bn32le(d)
	dax := bn32le(da)

	var aG, d_aG, da_G [32]byte
	curve25519.ScalarBaseMult(&aG, &ax)
	curve25519.ScalarBaseMult(&da_G, &dax)
	curve25519.ScalarMult(&d_aG, &dx, &aG)
	fmt.Printf("homomorphic  = %v\n", da_G == d_aG)
	fmt.Printf("---\n")

	// Check Failure sets
	lb0 := big.NewInt(0)
	ub0 := big.NewInt(0).Mul(x25519, big.NewInt(8))

	lb1 := big.NewInt(0).Lsh(big.NewInt(1), 255)
	ub1 := g.n

	fmt.Printf("fail(lb)     = %v\n", g.Fail(lb0))
	fmt.Printf("fail(ub)     = %v\n", g.Fail(ub0))
	fmt.Printf("fail(ub + h) = %v\n", g.Fail(big.NewInt(0).Add(ub0, g.h)))
	fmt.Printf("---\n")
	fmt.Printf("fail(lb - h) = %v\n", g.Fail(big.NewInt(0).Sub(lb1, g.h)))
	fmt.Printf("fail(lb)     = %v\n", g.Fail(lb1))
	fmt.Printf("fail(ub)     = %v\n", g.Fail(ub1))
	fmt.Printf("---\n")

	// Check bad delta generation
	db := g.BadDelta(a, lb1, ub1)
	dba, _ := g.Mult(d, a)
	fmt.Printf("clamped(d)   = %v\n", g.Clamped(db))
	fmt.Printf("fail(d*a)    = %v\n", g.Fail(dba))
	fmt.Printf("\n")

	// Generate a positive success case
	dp := random(big.NewInt(0), g.n)
	_, s := g.Mult(dp, a)
	for s.cP == 0 {
		dp = random(big.NewInt(0), g.n)
		_, s = g.Mult(dp, a)
	}
	printTestCase25519("pos", dp, a)

	// Generate a negative success case
	dn := random(big.NewInt(0), g.n)
	_, s = g.Mult(dn, a)
	for s.cP == 1 {
		dn = random(big.NewInt(0), g.n)
		_, s = g.Mult(dn, a)
	}
	printTestCase25519("neg", dn, a)

	// Generate a failure case
	printTestCase25519("fail", db, a)
}

func check448() {
	g := g448

	// Check that homomorphism holds
	a := random(big.NewInt(0), g.n)
	d := random(big.NewInt(0), g.n)
	da, _ := g.Mult(d, a)

	ax := bn56le(a)
	dx := bn56le(d)
	dax := bn56le(da)

	var aG, d_aG, da_G [56]byte
	curve448.ScalarBaseMult(&aG, &ax)
	curve448.ScalarBaseMult(&da_G, &dax)
	curve448.ScalarMult(&d_aG, &dx, &aG)
	fmt.Printf("homomorphic  = %v\n", da_G == d_aG)
	fmt.Printf("---\n")

	// Check Failure sets
	lb := big.NewInt(1)
	lb.Lsh(lb, 447)
	lb.Sub(lb, big.NewInt(0).Mul(x448, big.NewInt(4)))
	lb.Add(lb, g.h)

	ub := big.NewInt(1)
	ub.Lsh(ub, 447)
	ub.Sub(ub, g.h)

	fmt.Printf("fail(lb - h) = %v\n", g.Fail(big.NewInt(0).Sub(lb, g.h)))
	fmt.Printf("fail(lb)     = %v\n", g.Fail(lb))
	fmt.Printf("fail(ub)     = %v\n", g.Fail(ub))
	fmt.Printf("fail(ub + h) = %v\n", g.Fail(big.NewInt(0).Add(ub, g.h)))
	fmt.Printf("---\n")

	// Check bad delta generation
	db := g.BadDelta(a, lb, ub)
	dba, _ := g.Mult(db, a)
	fmt.Printf("clamped(d)   = %v\n", g.Clamped(db))
	fmt.Printf("fail(d*a)    = %v\n", g.Fail(dba))
	fmt.Printf("\n")

	// Generate a positive success case
	dp := random(big.NewInt(0), g.n)
	_, s := g.Mult(dp, a)
	for s.cP == 0 {
		dp = random(big.NewInt(0), g.n)
		_, s = g.Mult(dp, a)
	}
	printTestCase448("pos", dp, a)

	// Generate a negative success case
	dn := random(big.NewInt(0), g.n)
	_, s = g.Mult(dn, a)
	for s.cP == 1 {
		dn = random(big.NewInt(0), g.n)
		_, s = g.Mult(dn, a)
	}
	printTestCase448("neg", dn, a)

	// Generate a failure case
	printTestCase448("fail", db, a)
}

func main() {
	setup()

	fmt.Println("=== 25519 ===")
	check25519()

	fmt.Println("=== 448 ===")
	check448()
}
