# A076502 kernel-checked development

This development proves the literal recurrence identification and its
structural consequences. The entry point
is [Main.lean](Main.lean). The current source/axiom audit is
[verification.json](verification.json), with full compiler output in
[final-axioms.txt](build-logs/final-axioms.txt).

## Reproduce

Pinned environment: Lean 4.33.0, commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`; Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`.
The standalone fresh-build runner is invoked from the research package root:

```sh
python3 develop/clean_ci.py
```

This creates a fresh temporary Lake project, fetches pinned dependencies and
official Mathlib binary caches into a fresh directory, and compiles every
collaboration module from source. It does not reuse the local `trureturing`
checkout or local proof outputs. It does not bootstrap Mathlib or the compiler
from source. The result is recorded in `../ci-results/clean-build.json`, with
explicit execution provenance.

Alternatively, `lakefile.toml` and `lean-toolchain` support a build directly
in this checkout. From this directory, install the dependencies and run:

```sh
lake update
lake exe cache get
lake env python3 ../audit_lean.py
```

The Python builder compiles the local import closure topologically and logs
each rebuilt module. It prepends this directory to `LEAN_PATH`; generated
`.olean` files are local build products and are not distributed as evidence.
The audit checks source hashes, dependency freshness, forbidden proof
shortcuts, and the axiom closure of the final closed theorems.
Some kernel certificate checks take several minutes.

The September 23 isolated run passed: 69 local modules rebuilt from source,
18 final theorem closures checked, and all four runner stages exited zero.
The checked source hashes are identical to this package's source closure.

## Checked Statements

The recurrence is `a(0)=0`, `a(1)=1`, and
`a(n)=n-a(n-a(n-a(n-1)))` for every `n >= 2`.
`ComputableSequence.eval` is an explicit computable implementation. Its
syntactic recursion clamps are proved inactive. All sequence theorems also
apply to any natural-valued function satisfying the literal recurrence and
these initial values.

| Result | Main proof source |
| --- | --- |
| Greedy representation existence, uniqueness, and exact seven-state recognition | `GreedyRepresentation.lean` |
| Carry and two-position-delay semantics; finite product, projection, and inclusion certificates | `WordArithmetic.lean`, `AutomataCertificate.lean`, `Generated/` |
| Totality and full recurrence identification with `shift + E` | `FinalIdentification.lean`, `GraphCandidate.lean` |
| Exact D-DFAO first-difference formula | `FirstDifference.lean` |
| Global discrepancy, corrected exact floor-offset set `{-1,0,1,2}`, and all four witnesses | `SequenceConsequences.lean`, `OffsetWitnesses.lean` |
| Paper bound `-1.049234 < a(n)-cn < 1.155081` for every n | `TightGlobalBound.lean`, `TightSuffixSoundness.lean`, `TightSuffixCertificate.lean` |
| Limit `a(n)/n -> c`, where `c^3-c^2+2c-1=0` | `FinalIdentification.lean`, `Discrepancy.lean` |
| Genuine infinite word from the explicit 26-letter non-erasing morphism and non-erasing output morphism; all-index equality with first differences | `Morphic.lean`, `MorphicEnumeration.lean`, `MorphicIdentification.lean` |
| Binary increments, monotonicity, irrational slope, nonperiodicity, and 4-balanced factor sums | `MorphicIdentification.lean`, `IrrationalSlope.lean`, `SequenceConsequences.lean` |
| Literal word counts, frequency of 1, 4-balanced words, and word nonperiodicity | `WordConsequences.lean` |
| Least balance constant exactly 4, with length-72 factors containing 43 and 39 ones | `BalanceSharpness.lean` |
| Computable rational intervals enclosing both global discrepancy extrema at every cutoff; widths tend to zero and all endpoints converge | `EffectiveExtrema.lean` |

The exact offset witnesses are `n=1167,2,1,93`, giving offsets
`-1,0,1,2`, respectively. These are kernel-checked evaluations, not only
Python observations. The initial K=20 Bellman certificate proves
`-11/10 < a(n)-cn < 6/5`, enough for all four-offset and balance arguments.
The additional K=105 certificate with a 160-bit dyadic slope bracket proves
the sharper six-decimal bound stated in the paper. Its finite Bellman data
are independently checked by kernel reduction. The generator is
`../generate_tight_suffix_lean.py`.

The morphic proof uses direct enumeration: at each fixed length `m`, the
state-morphism iterate enumerates legal padded words, its root count is
exactly `U_m`, and each word's numeric value is its exact rank. It does not
assume a general abstract-numeration theorem or a finite-prefix match.

The effective extrema algorithm is explicit but intentionally exhaustive:
search `n < U(K+16)`, bisect the slope root to precision `4K+64`, and add the
proved geometric error. This establishes computability with no unproved
oracle or optimal-path premise. It is distinct from the efficient Python
suffix dynamic program used for the K=200 decimal values.

## Trust And Scope

Final theorem closures use only `propext`, `Classical.choice`, and `Quot.sound`.
There are no `sorry` terms, additional axioms, `native_decide`, or
`decide +native`. Finite computations using `decide +kernel` are checked by
the Lean kernel. Python generators are untrusted certificate producers;
their concrete transition, closure, and Bellman data must pass Lean checks.

Still separate from the formalized conclusions:

- The reported K=200 narrow decimal enclosures are exact rational
  computational certificates, not separately asserted Lean theorems.
- Equality with Cloitre's original six-letter candidate remains open.
- No minimality of the 26-letter presentation is claimed. The balance constant
  is proved optimal. Extrema attainment and equality to asymptotic extrema remain
  open questions.
