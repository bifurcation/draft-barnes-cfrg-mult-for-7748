from random import getrandbits

def xgcd(a, b):
    """return (g, x, y) such that a*x + b*y = g = gcd(a, b)"""
    x0, x1, y0, y1 = 0, 1, 1, 0
    while a != 0:
        q, b, a = b // a, a, b % a
        y0, y1 = y1, y0 - q * y1
        x0, x1 = x1, x0 - q * x1
    return b, x0, y0

class Group:
    def __init__(self, n, b, h):
        self.n = n
        self.b = b
        self.h = h

    def clamp(self, x):
        return (x - (x % self.h)) | (1 << self.b)

    def clamped(self, x):
        return self.clamp(x) == x

    def fail(self, x):
        return not self.clamped(x) and not self.clamped(self.n - x)

    def mult(self, d, sk):
        dc = self.clamp(d)
        skc = self.clamp(sk)
        skP = (dc * skc) % self.n
        skN = self.n - skP
        cP = skN >> self.b
        if 1 - cP == 1:
            skP, skN == skN, skP
        return skP

    def bad_delta(self, sk, lb):
        skc = self.clamp(sk)
        gcd, ai, ni = xgcd(skc, self.n)
        if gcd != self.h:
            raise Exception("Unexpected gcd")

        # Target is first multiple of cofactor squared above lower bound.  This
        # ensures that the low-order bits of the delta are clamped.
        h2 = self.h * self.h
        t = lb + h2 - (lb % h2)
        
        #          ai * a = h         (mod n)
        # => (c * ai) * a = c * h = t (mod n)
        c = t // self.h
        d = (c * ai) % self.n

        # Since the failure set is closed under negation, either d or its
        # negative will suffice
        if self.clamped(d):
            return d
        elif self.clamped(self.n - d):
            return self.n - d

        # This process should succeed with overwhelming probability, for the
        # same reasons that failed updates overwhelmingly succeed
        raise Exception("Rare failure")

# Check bounding conditions

## X25519
def check_25519():
    print("=== Curve25519 ===")
    x = 0x14def9dea2f79cd65812631a5cf5d3ed
    h = 8
    n = h*((1 << 252) + x)
    g = Group(n, 254, h)

    # Range 1
    lb = 0
    ub = 8*x 
    print("fail(lb)     = {}".format(g.fail(lb)))
    print("fail(ub)     = {}".format(g.fail(ub)))
    print("fail(ub + h) = {}".format(g.fail(ub + h)))
    print("---")
    
    # Range 2
    lb = (1 << 255)
    ub = n 
    print("fail(lb-h)   = {}".format(g.fail(lb - h)))
    print("fail(lb)     = {}".format(g.fail(lb)))
    print("fail(ub)     = {}".format(g.fail(ub)))
    print("---")

    # Find an unsuccessful delta
    a = getrandbits(256)
    d = g.bad_delta(a, lb)
    da = g.mult(d, a)
    print("clamped(d)   = {}".format(g.clamped(d)))
    print("fail(d*a)    = {}".format(g.fail(da)))
    print("")
check_25519()

## X448
def check_448():
    print("=== Curve448 ===")
    x = 0x8335dc163bb124b65129c96fde933d8d723a70aadc873d6d54a7bb0d
    h = 4
    n = h*((1 << 446) - x)
    g = Group(n, 447, h)

    # Verify the failure set
    lb = (1 << 447) - (4*x) + h
    ub = (1 << 447) - h
    print("fail(lb-h)   = {}".format(g.fail(lb - h)))
    print("fail(lb)     = {}".format(g.fail(lb)))
    print("fail(ub)     = {}".format(g.fail(ub)))
    print("fail(ub+h)   = {}".format(g.fail(ub + h)))
    print("---")

    # Find an unsuccessful delta
    a = getrandbits(448)
    d = g.bad_delta(a, lb)
    da = g.mult(d, a)
    print("clamped(d)   = {}".format(g.clamped(d)))
    print("fail(d*a)    = {}".format(g.fail(da)))
    print("")
check_448()
