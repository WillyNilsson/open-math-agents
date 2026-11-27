"""Verify the 1,048,576-cell C1a witness from its 524,288-cell parent.

Standard library: python -I -B split.py witness.json
Independent NTT cross-check (requires NumPy): python -I -B split.py witness.json --ntt verify_ntt.py
The recipe split.json accompanies this script. witness.json and verify_ntt.py
are from the parent C1a-bound package.

For N equal cells of width D=1/(2N) on [-1/4,1/4] with heights a_i,
the integral is D*sum(a). The convolution is linear between grid knots;
at -1/2+(k+1)D it is D*c_k, where c_k=sum_i a_i a_(k-i) with zero
extension. Thus the certified upper bound is 2N*max(c)/sum(a)^2.

Write e,o for the two integer multipliers. Splitting every cell replaces
A(X)=sum a_i X^i by (e+oX)A(X^2). On squaring, fine coefficients at
2k and 2k+1 are e^2 c_k+o^2 c_(k-1) and 2eo c_k, respectively.
The direct NTT check instead transforms the fine heights themselves.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import runpy


def require(test, message):
    if not test:
        raise ValueError(message)


def parent_coefficients(heights):
    # Each digit is at most sum(a_i^2) by Cauchy-Schwarz on shifted vectors.
    # A strictly larger byte-aligned radix prevents carries when we square.
    width = max(1, (sum(x*x for x in heights).bit_length() + 7) // 8)
    packed = int.from_bytes(b"".join(x.to_bytes(width, "little") for x in heights), "little")
    count = 2*len(heights)-1
    raw = memoryview((packed * packed).to_bytes(count*width, "little"))
    return [int.from_bytes(raw[i:i+width], "little") for i in range(0, len(raw), width)]


def fine_coefficients(parent, even, odd):
    e2, o2, eo2 = even*even, odd*odd, 2*even*odd
    previous = 0
    for x in parent:
        yield e2*x + o2*previous
        yield eo2*x
        previous = x
    yield o2*previous


def report(label, n, mass, coefficients, expected):
    maximum, lags, total, count = -1, [], 0, 0
    for k, c in enumerate(coefficients):
        count += 1
        total += c
        if c > maximum:
            maximum, lags = c, [k]
        elif c == maximum:
            lags.append(k)
    require(count == 2*n-1 and total == mass*mass, label + " coefficient total")
    require((n, mass, maximum, lags) ==
            (expected["N"], int(expected["sum_a"]), int(expected["max_conv"]), expected["peak_lags"]),
            label + " size, mass, maximum or peak set mismatch")
    value = Fraction(2*n*maximum, mass*mass)
    require(value == recorded_fraction(expected), label + " rational mismatch")
    print(f"{label}: N={n}, S={mass}, M={maximum}, zero-based peak lags={lags}")
    return value


def recorded_fraction(record):
    return Fraction(int(record["numerator"]), int(record["denominator"]))


def decimal(value):
    with localcontext() as ctx:
        ctx.prec = 64
        return Decimal(value.numerator) / Decimal(value.denominator)


def main():
    ap = argparse.ArgumentParser(description="Verify the second half-cell refinement of C1a.")
    ap.add_argument("witness", type=Path)
    ap.add_argument("--ntt", type=Path, help="also compare every fine coefficient with the pinned direct NTT checker")
    args = ap.parse_args()
    r = json.loads(Path(__file__).with_name("split.json").read_bytes())
    require(r["format"] == "c1a-uniform-half-cell-split-v1", "Unrecognized recipe")
    raw = args.witness.read_bytes()
    require(sha256(raw).hexdigest() == r["parent"]["sha256"], "Incorrect parent witness hash")
    h = json.loads(raw)["weights"]
    require(h and all(type(x) is int and x >= 0 for x in h) and any(h), "Invalid heights")
    e, o = r["multipliers"]["even"], r["multipliers"]["odd"]
    require(type(e) is int and e > 0 and type(o) is int and o > 0, "Invalid split multipliers")
    n, mass = len(h), sum(h)
    c = parent_coefficients(h)
    old = report("Parent", n, mass, c, r["parent"])
    v = report("Split", 2*n, (e+o)*mass, fine_coefficients(c,e,o), r["fine"])
    previous = recorded_fraction(r["pr418"])
    require(v < old < previous, "Strict improvements not established")
    print("Exact bound:", v)
    print("Decimal approximation:", decimal(v))
    for label, reference in (("parent",old), ("PR #418",previous)):
        gain = reference-v
        print(f"Decrease from {label}: {gain} (approximately {decimal(gain)})")

    if args.ntt:
        require(sha256(args.ntt.read_bytes()).hexdigest() == r["direct_ntt"]["sha256"],
                "Incorrect independent NTT checker hash")
        ntt = runpy.run_path(str(args.ntt))
        fine = [factor*x for x in h for factor in (e,o)]
        primes = [p for p,_ in ntt["primes_for"](sum(x*x for x in fine))]
        require(primes == r["direct_ntt"]["primes"], "Unexpected CRT moduli")
        direct = ntt["convolution"](fine)
        require(len(direct) == 2*len(fine)-1, "Incorrect NTT convolution length")
        require(all(int(y) == z for y,z in zip(direct, fine_coefficients(c,e,o))),
                "Direct NTT disagreed with a fine coefficient")
        print(f"Independent NTT/CRT agreed on all {len(direct)} fine coefficients using {len(primes)} primes.")


if __name__ == "__main__":
    main()

