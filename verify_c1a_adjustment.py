"""Check our C1a multi-cell witness or replay the earlier one-cell experiment.

Run: python verify_c1a_adjustment.py witness.json
Giving the original witness_262144_v3.json replays the one-cell experiment.

Starting witness by Will Kirschenman, refined from PR 408:
https://raw.githubusercontent.com/willk30/optimization-certificates/c1ead4cfdde623a57d3a60f8b8abe56337095927/c1a-upper/results/witness_262144_v3.json
https://github.com/teorth/optimizationproblems/pull/418

For N equal-width cells on [-1/4,1/4] with nonnegative integer heights h,
the autoconvolution is linear between adjacent grid knots. Its maximum
divided by the squared mass is 2*N*max(h*h)/sum(h)^2. This script checks
both complete discrete autoconvolutions using exact integer squaring.
"""
from argparse import ArgumentParser
from decimal import Decimal, getcontext
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path


def objective(heights):
    # Cauchy-Schwarz bounds every convolution coefficient by sum(h_i^2).
    width = (sum(a*a for a in heights).bit_length()+7)//8
    packed = int.from_bytes(b"".join(a.to_bytes(width, "little") for a in heights), "little")
    squared = (packed*packed).to_bytes((2*len(heights)-1)*width, "little")
    peak = max(int.from_bytes(squared[i:i+width], "little") for i in range(0, len(squared), width))
    return peak, Fraction(2*len(heights)*peak, sum(heights)**2)


def main():
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("witness", type=Path)
    args = parser.parse_args()
    raw = args.witness.read_bytes()
    fingerprint = sha256(raw).hexdigest()
    heights = json.loads(raw)["weights"]
    if fingerprint == "e413bfe3ca5248ebcb83474c19d432e265738c16c698d1054d4300b0eb294112":
        if len(heights) != 524288 or any(type(a) != int or a < 0 for a in heights):
            raise ValueError("Invalid multi-cell witness")
        peak, bound = objective(heights)
        expected = Fraction(519430314903936621654612615023564348717838184096989184,
                            345672820315193691904670643895864696282762768089237289)
        original = Fraction(24440309691768679463247675392,16264647129627086646956500225)
        if peak != 495367350486694928793537726424755428998792823884 or bound != expected or not bound < original:
            raise ValueError("Multi-cell certificate failed")
        getcontext().prec = 50
        print(f"Verified {len(heights):,} cells. Exact C1a upper bound: {bound}")
        print("Decimal:", Decimal(bound.numerator)/Decimal(bound.denominator))
        return
    if fingerprint != "3d395c6a3ce7616d2ff4360b3e78484663a8a0f28bdf7ec641b4875ab6908775":
        raise ValueError("Unexpected witness hash")
    if len(heights) != 262144 or any(type(a) != int or a < 0 for a in heights) or heights[121425] != 0:
        raise ValueError("Unexpected heights")
    peak, original = objective(heights)
    heights[121425] = 127
    new_peak, adjusted = objective(heights)
    if original != Fraction(24440309691768679463247675392,16264647129627086646956500225):
        raise ValueError("Original objective mismatch")
    if adjusted != Fraction(152751935573554246645297971200,101654044560209783247377953801):
        raise ValueError("Adjusted objective mismatch")
    if new_peak != peak or adjusted >= original:
        raise ValueError("The edit did not improve the original fraction at the same peak")
    getcontext().prec = 40
    for name, value in (("Original", original), ("Adjusted", adjusted), ("Decrease", original-adjusted)):
        print(f"{name}: {value} = {Decimal(value.numerator) / Decimal(value.denominator)}")


if __name__ == "__main__":
    main()
