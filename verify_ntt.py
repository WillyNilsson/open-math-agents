"""Verify an integer step-function autocorrelation witness using independent NTTs and CRT.

Requires Python 3 and NumPy. The only input is a JSON object with integer
weights. The exact step-function bound is 2*N*max(a*a)/(sum a)^2. No claimed
coefficient, peak or bound is used to reconstruct the convolution.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
import json
from math import isqrt,prod
from pathlib import Path
from time import perf_counter
import numpy as np

PRIMES = (998244353, 1004535809, 469762049, 167772161)
EXTRA = ((1224736769, 3), (754974721, 11), (2013265921, 31), (1811939329, 13))
PR418_SHA = "3d395c6a3ce7616d2ff4360b3e78484663a8a0f28bdf7ec641b4875ab6908775"


def inverse_order(n):
    idx = np.array([0], dtype=np.int64)
    while len(idx) < n:
        nxt = idx * 2
        idx = np.concatenate((nxt, nxt + 1))
    return idx


def transform(values, powers, p, reorder):
    a = values[reorder].copy()
    m = 2
    while m <= len(a):
        h = m//2
        blocks = a.reshape(-1, m)
        u = blocks[:, :h].copy()
        v = blocks[:, h:] * powers[::len(a)//m][:h] % p
        blocks[:, :h] = (u + v) % p
        blocks[:, h:] = (u - v) % p
        m *= 2
    return a


def square_mod(a,p,order,generator=3):
    n = len(order)
    assert all(p%q for q in range(2,isqrt(p)+1))
    assert (p-1)%n == 0 and p*p < 2**63
    root = pow(generator,(p-1)//n,p)
    assert pow(root,n,p)==1 and (n==1 or pow(root,n//2,p)!=1)
    powers = np.empty(n,dtype=np.int64)
    w = 1
    for i in range(n):
        powers[i] = w
        w = w*root%p
    x = np.zeros(n,dtype=np.int64)
    x[:len(a)] = np.array([v%p for v in a],dtype=np.int64)
    freq = transform(x,powers,p,order)
    squared = freq*freq%p
    invp = np.concatenate((powers[:1], powers[:0:-1]))
    return transform(squared,invp,p,order)*pow(n,-1,p)%p


def primes_for(ceiling):
    choices=[(p,3) for p in PRIMES]
    for item in EXTRA:
        if prod(p for p,g in choices)>ceiling:break
        choices.append(item)
    assert prod(p for p,g in choices)>ceiling
    return choices


def convolution(a):
    size = len(a)
    assert size>0 and all(type(x) is int and x>=0 for x in a)
    # Cauchy-Schwarz bounds any coefficient by sum_i a_i^2. Thus CRT
    # reconstructs each integer uniquely from its residues below this bound.
    ceiling = sum(x*x for x in a)
    choices=primes_for(ceiling)
    n = 1<<(2*size-2).bit_length()
    reorder = inverse_order(n)
    coeff = np.zeros(n, dtype=object)
    mod = 1
    for p,g in choices:
        r = square_mod(a,p,reorder,g).astype(object)
        delta = (r - coeff%p)*pow(mod,-1,p)%p
        coeff += delta*mod
        mod *= p
    assert not any(coeff[2*size-1:]) and int(max(coeff))<=ceiling
    assert sum(coeff)==sum(a)**2
    return coeff[:2*size-1]

def load_weights(data,seed=None):
    if isinstance(data,list):return data
    if "weights" in data:return data["weights"]
    if "delta" not in data or seed is None:raise ValueError("Provide --seed for a sparse delta witness")
    raw=seed.read_bytes()
    if sha256(raw).hexdigest()!=PR418_SHA:raise ValueError("Unrecognized PR418 base")
    h=[data["base_scale"]*v for v in json.loads(raw)["weights"]]
    for j,v in data["delta"]:h[j]+=v
    return h


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("witness",type=Path)
    parser.add_argument("--source-418",action="store_true")
    parser.add_argument("--seed",type=Path)
    parser.add_argument("--out",type=Path)
    args=parser.parse_args()
    t=perf_counter()
    raw=args.witness.read_bytes()
    data=json.loads(raw)
    h=load_weights(data,args.seed)
    S=sum(h); n=len(h)
    assert S>0
    if args.source_418:assert sha256(raw).hexdigest()==PR418_SHA
    coeff=convolution(h)
    M=int(max(coeff)); peak=int(np.argmax(coeff)); total=int(np.count_nonzero(coeff==M))
    val=Fraction(2*n*M,S*S)
    if args.source_418:
        assert (S,M,peak,total)==(int(data["sum_a"]),int(data["max_conv"]),data["first_peak_lag"],data["peak_count"])
        assert val==Fraction(int(data["numerator"]),int(data["denominator"]))
    with localcontext() as ctx:
        ctx.prec=60
        dec=str(Decimal(val.numerator)/Decimal(val.denominator))
    record=dict(sha256=sha256(raw).hexdigest(),N=n,sum_a=str(S),max_conv=str(M),
                first_peak_lag=peak,peak_count=total,numerator=str(val.numerator),
                denominator=str(val.denominator),decimal=dec,primes=[p for p,g in primes_for(sum(x*x for x in h))])
    if args.out:args.out.write_text(json.dumps(record,indent=2)+"\n")
    print(json.dumps(record))
    print("Exact verification seconds",round(perf_counter()-t,3))


if __name__=="__main__":main()

