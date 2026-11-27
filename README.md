# C1a upper-bound certificates

Supporting material for the Left to Solve problem [Constant1a.mem_Ico_c1a](https://lefttosolve.com/p/Constant1a.mem_Ico_c1a), submitted by Willy Nilsson (`WillyNilsson`) with OpenAI Codex. The project PR identifies the smaller witness that fits its one-file checker. The larger constructions documented here improve on the strongest public upper-bound submission we found in our November 27, 2026 search.

| Construction | Upper bound, rounded upward | Verification |
| --- | --- | --- |
| 524,288 equal cells | 1.502664613406128415 | Lean 4.33.1, packed integer squaring, and modular transforms with Chinese remainder reconstruction |
| 1,048,576 equal cells | 1.502664613406125390 | Exact integer squaring of the parent followed by the subdivision identities, and a separate modular reconstruction of every coefficient directly from the fine heights |

The Lean theorem in this repository covers the first row. The finer construction improves that value by approximately `3.02543e-15`. Its exact ratio is

```text
16124353801444301117880474240400261526455525552208409537172579155968
/ 10730507431658250947299700927335358497863186863726223329858730545929
```

## Replay

Python 3 can check both rows with the standard library.

```sh
python -B verify_c1a_adjustment.py witness.json
python -B split.py witness.json
```

The second command constructs all fine convolution coefficients from the exact parent convolution. To compare each coefficient with a direct transform of the fine witness, install NumPy and run

```sh
python -B split.py witness.json --ntt verify_ntt.py
```

For the Lean replay, use Lean 4.33.1 and a built `google-deepmind/formal-conjectures` checkout at [9097e2f90e66d2f6244209cb1c07f7120d17ec53](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/OptimizationConstants/1a.lean) with its pinned Mathlib cache. The script generates the packed data from `witness.json`.

```sh
python -B lean/verify.py witness.json --fc /path/to/formal-conjectures --bin /path/to/lean/bin --exact-receipt manifest.json
```

The witness hash, exact fraction, and axiom audit for `C1aUpper.c1a_upper_verified` are in `manifest.json`. The audit reports `propext`, `Classical.choice`, and `Quot.sound`.

## Construction and credit

The starting heights are from [Will Kirschenman's PR #418](https://github.com/teorth/optimizationproblems/pull/418), building on [Josh Hurst's PR #408](https://github.com/teorth/optimizationproblems/pull/408). The submitted 524,288-cell construction comes from joint optimization of many heights on the original 262,144-cell grid and a dyadic subdivision. The analytic bridge and Kronecker lemmas are from [Kirschenman's pinned certificate](https://github.com/willk30/optimization-certificates/tree/c1ead4cfdde623a57d3a60f8b8abe56337095927/c1a-upper). The upstream MIT notices are included.

For the second row, replace each height `a` in `witness.json` by the two heights `22286275*a` and `22286277*a`, in that order. If the parent generating polynomial is `A(X)`, the fine polynomial is `(22286275 + 22286277*X) A(X²)`. Squaring it gives an exact integer check at every lag. For `N` equal cells with total height `S` and maximum convolution coefficient `M`, the upper bound is `2*N*M/S²`. The fine witness has `N = 1048576`, `S = 26205962596823801095882900708080616`, and `M = 492076226850717197200942207043465012404038255377453904332659276`. The sole maximizing lag is 1732056, using zero-based indexing.
