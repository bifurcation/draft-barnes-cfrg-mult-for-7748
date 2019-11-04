---
title: Homomorphic Multiplication for X25519 and X448
abbrev: Multiplication
docname: draft-barnes-cfrg-mult-for-7748-latest
date:
category: info

ipr: trust200902
keyword: Internet-Draft

stand_alone: yes
pi: [toc, sortrefs, symrefs]
updates: 7748

author:
 -  ins: R. L. Barnes
    name: Richard L. Barnes
    org: Cisco
    email: rlb@ipv.sx
 -  ins: J. Alwen
    name: Joël Alwen
    org: Wickr
    email: jalwen@wickr.com
 -  ins: S. Corretti
    name: Sandro Corretti
    org: IOHK
    email: corettis@gmail.com

informative:

--- abstract

In some contexts it is useful for holders of the private and public parts an
elliptic curve key pair to be able to independently apply an updates to those
values, such that the resulting updated public key corresponds to the updated
private key.  Such updates are straightforward for older elliptic curves, but
for Curve25519 and Curve448, the "clamping" prescribed for scalars requires some
additional processing.  This document defines a multiplication procedure that
can be used to update Curve25519 and Curve448 key pairs.  This algorithm can
fail to produce a result, but only with negligible probability.  Failures can
be detected by the holder of the private key.

--- middle

# Introduction

In some contexts it is useful for holders of the private and public parts of an
elliptic curve key pair to be able to independently apply an updates to those
values, such that the resulting updated public key corresponds to the updated
private key.  [[ TODO: Cite examples, security properties ]]

Such updates are straightforward with traditional elliptic curves, such as the
NIST and Brainpool curves, or with the proposed Ristretto curve.  In these
curves, multiplication of points by scalars is a homomorphism with regard to
multiplication of scalars, so a key pair can be updated by multiplying the
private key and the same "delta" scalar.  In other words, the following diagram
commutes for all `d`, where `d\*` represents scalar multiplication by `d` and
`\*G` represents multiplication of a scalar with the base point of the curve:

~~~
          *G
Scalars ------> Points
   |              |
d* |              | d*
   V              V
Scalars ------> Points
          *G
~~~

The Curve25519 and Curve448 functions defined in RFC 7748, however, require
scalars to be "clamped" before point multiplication is performed, which breaks
this homomorphism.  In particular, scalars are passed through the
`decodeScalar25519` or `decodeScalar448` functions, respectively, which force
a high-order bit to be set.  Since this high-order bit is not guaranteed to be
set in the product of two such numbers, the product of of two scalars may not
represent a valid private key.  In fact, there are valid X25519/X448 curve
points which cannot be Curve25519/Curve448 public keys, because their discrete
logs do not have the correct high bit set.

Fortunately, Curve25519 and Curve448 use only one coordinate to represent curve
points, which means they are insensitive to the sign of the point, so a scalar
private key and its negative result in the same public key.  And if a given
scalar does not have the correct bit set, then its negative modulo the curve
order almost certainly does.  (We quantify these ideas below.)  This allows us
to construct an amended multiplication routine that succeeds with overwhelming
probability, and where the failure cases are detectable by the holder of the
private key.

The remainder of this document describes these algorithms, quantifies the
failure cases and the resulting probabilities of failure, and discusses how
failures can be detected.


# Updating Curve25519 / Curve448 key pairs

The following procedures allow for updating Curve25519 / Curve448 public keys
and private keys in constant time.  The values `sk` and `pk` represent the
private and public keys of the key pair, and the value `d` represents a "delta"
scalar being applied.  All arithmetic operations are performed modulo the order
`n` of the relevant curve:

* Curve25519:
  * `x = 0x14def9dea2f79cd65812631a5cf5d3ed`
  * `n = 8 * (2^253 + x)`
  * `b = 254`
* Curve448:
  * `x = 0x8335dc163bb124b65129c96fde933d8d723a70aadc873d6d54a7bb0d`
  * `n = 4 * (2^446 - x)`
  * `b = 447`

~~~
def updatePublic(d, pk):
  return CurveN(d, pkI)

def updatePrivate(d, sk):
  dc = decodeScalar(d)
  skc = decodeScalar(sk)
  skP = dc * skc
  skN = n - skP
  cP = (skP >> b) & 1
  cswap(1 - cP, skP, skN)
  return skP
~~~

The pulic operation is clearly just a normal DH operation in the relevant curve.
The private operation computes the product of the delta with the private key as
well as its negative modulo the curve order.  If the product does not have the
correct bit set, then the cswap operation ensures that that the negative is
returned.

If `updatePrivate` and `updatePublic` are called on both halves of a key pair,
and `updatePrivate` produces a valid private key (with the relevant high bit
set), then the output private and public keys will correspond to each other.
(That is, the public key will equal the private key times the base point.)  If
the `updatePrivate` function does not return a valid private key, then the
update has failed, and the delta `d` cannot be used with this key pair.

# Failure Cases

An update of a private key `sk` by a delta `d` fails if and only if neither
`d*sk` or `n - d*sk` has the relevant bit set.  In this section, we will assume
that for uniform `d`, this product `c = d*sk` is uniformly distributed among
scalars modulo n.  From this assumption, we can describe the set of values `c`
for which updates fail, and thus estimate the probability that an update will
fail.

In general, an update fails if neither `c` nor its negative has the relevant
high bit set, i.e., if they are not in the range `[M, N]`, where `M = 2^b` and
`N = 2^{b+1} - 1`.  So our failure criterion is:

~~~
    (c < M || c > N) && ((n-c) < M || (n-c) > N)
<=> (c < M || c > N) && (c < n-N || c > n-M)
~~~

So the probability of failures is proportional to the size of the set where this
conditions applies.  In the following subsections, we will calculate these
values for Curve25519 and Curve448.

## Curve25519

In the case of Curve25519, the following values apply:

```
    b = 254
    n = 8 * (2^253 + x)
      = 2^255 + 8x
    M = 2^254
    N = 2^255 - 1
n - M = (2^255 + 8x) - 2^254
      = 2^254 + 8x
n - N = 8x + 1
```

Thus we have `n - N < M < n-M < N`, so the failure set `F` and the failure
probability `|F|/n` are as follows:

```
    F = [0, n-N) U (N, n]
      = [0, 8x + 1) U (2^255 - 1, 2^255 + 8x]
|F|/n = (2 * 8x) / (2^255 + 8x)
      < 2^130 / 2^255 (since x < 2^125)
      = 2^-125
```

## Curve448

In the case of Curve448, the following values apply:

```
    b = 447
    n = 4 * (2^446 - x)
      = 2^448 - 4x
    M = 2^447
    N = 2^448 - 1
n - M = (2^448 - 4x) - 2^447
      = 2^447 - 4x
n - N = 1 - 4x
```

Thus we have `n - N < 0 < n - M < M < N`, so the failure set `F` and the failure
probability `|F|/n` are as follows:

```
    F = (n-M, M)
      = (2^447 - 4x, 2^447)
|F|/n = (4x - 1) / (2^448 - 4x)
      < 2^226 / 2^448            (since x < 2^224)
      = 2^-222
```

# Protocol Considerations

Protocols making use of the update mechanism defined in this document should
account for the possibility that updates can fail.  As described above, entities
updating private keys can tell when the update fails.  However, entities that
hold only the public key of a key pair will not be able to detect such a
failure.  So when this mechanism is used in a given protocol context, it should
be possible for the private-key updater to inform other actors in the protocol
that a failure has occurred.

# Security Considerations

[[ TODO: Comment on whether this algorithm achieves the security objective
stated in the introduction ]]

The major security concerns with this algorithm are implementation-related.  The
`updatePrivate` function requires access to the private key in ways that are
typically not exposed by HSMs or other limited-access crypto libraries.
Implementing key updates with such limited interfaces will require either
exporting the private key or implementing the update algorithm internally to the
HSM/library.  (The latter obviously being preferable.)

As an algorithm involving secret key material, the `updatePrivate` function
needs to be implemented in in a way that does not leak secrets through side
channels.  While the algorithm specified above is logically constant-time, it
reques that multiplication, subtraction, and conditional swap be implemented in
constant time.

# IANA Considerations

This document makes no request of IANA.

---back

# Test Vectors

All values are presented as little-endian integers.  An implementation should
verify that the following relations hold:

* sk1 = updatePriv(d, sk0)
* pk1 = updatePub(d, pk0)
* pk1 = CurveN(sk1)

## Curve25519

Successful update (no swap):

~~~
sk0  bda28911417a37f841286befb17750e6d0f9468525b4ec120b234c9c75ab1397
pk0  30c7eaaabd8193ca1c1d2b291817ed718cdbf682dc48524466d4d469d97f6d0d
d    fb1808cf0e5a462e5f22f1c5b5a2fc9ae2e0e3a1e9c64f581633cc3b6791d387
dC   f81808cf0e5a462e5f22f1c5b5a2fc9ae2e0e3a1e9c64f581633cc3b6791d347
skC  b8a28911417a37f841286befb17750e6d0f9468525b4ec120b234c9c75ab1357
skP  e8fa5352c1664de559ef397c7d054db4f437a4d6bc35cef64b25550cb3084c45
skN  80a45a9511b245db58f7829b77c9aaf20bc85b2943ca3109b4daaaf34cf7b33a
cP   1
sk1  e8fa5352c1664de559ef397c7d054db4f437a4d6bc35cef64b25550cb3084c45
pk1  d5b371eda213982efef0a9b18c699bba115e7ddf229bc675e8637910d7e5b54f
~~~

Successful update (swap):

~~~
sk0  0f8c14649988ced00a5168818af2eddcd5a6516465398cf9b6954e51c8e210e5
pk0  ad2151ec8ffdc558262b05b6303cbaeefc5591571ae36a5c13af361bf3d32f03
d    eb656cf4aa02571861364aa4d12ec5f94d73544a57f82c9563a0d1bee276e004
dC   e8656cf4aa02571861364aa4d12ec5f94d73544a57f82c9563a0d1bee276e044
skC  088c14649988ced00a5168818af2eddcd5a6516465398cf9b6954e51c8e21065
skP  d01412f7ef261fc18df5a27ecc24f216075f22fe387e774e2d878a45dd02f73d
skN  988a9cf0e2f173ff24f1199928aa0590f9a0dd01c78188b1d27875ba22fd0842
cP   0
sk1  988a9cf0e2f173ff24f1199928aa0590f9a0dd01c78188b1d27875ba22fd0842
pk1  dc9ed70b0e5010f2c7a2b0cdb8eef0fb47afa0aad2da96f9f2b9db238728e90c
~~~

[[ TODO: Failure case ]]

## Curve448

[[ TODO ]]

# Acknowledgements

Thanks to Mike Hamburg for reviewing an early version of the ideas that led to
this document.

