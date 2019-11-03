class Group:
    def __init__(self, n, b):
        self.n = n
        self.b = b

    def clamped(self, x):
        # equivalently: return x >= (1 << self.b) and x < (1 << (self.b+1))
        return (x >> self.b) == 1

    def fail(self, c):
        return not self.clamped(c) and not self.clamped(self.n - c)
    
    def check_bounds(self, lb, ub):
        for c in [lb, lb+1, ub-1, ub]:
            print(self.fail(c))

x25519 = 0x14def9dea2f79cd65812631a5cf5d3ed
n25519 = 8*((1 << 252) + x25519)
g25519 = Group(n25519, 254)

x448 = 0x8335dc163bb124b65129c96fde933d8d723a70aadc873d6d54a7bb0d
n448 = 4*((1 << 446) - x448)
g448 = Group(n448, 447)

# Check bounding conditions

## X25519
def check_25519():
    print("=== Curve25519 ===")
    # Range 1
    lb = 0
    ub = 8*x25519 + 1
    g25519.check_bounds(lb, ub)

    print("---")
    
    # Range 2
    lb = (1 << 255) - 1
    ub = (1 << 256) - 1
    g25519.check_bounds(lb, ub)
check_25519()

## X448
def check_448():
    print("=== Curve448 ===")
    lb = (1 << 447) - (4*x448)
    ub = (1 << 447)
    g448.check_bounds(lb, ub)
check_448()
