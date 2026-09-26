# Independent Walnut replay

The successful report is `../automata-results/walnut.json`. All six checks
are TRUE: adder totality, graph totality, value bounds, positivity, literal
nested recurrence, and first differences.

Version: Walnut 7.1.0, tag `v7.1.0`, upstream commit
`67e69c248d07324b25de1d4a498e877ac504999a`.
Source: https://github.com/Walnut-Theorem-Prover/Walnut
The jar used in this session has SHA256
`dab1c00fef7408ea44c1b31a4897a9325930539034a3c79cf570f61c034616df`.
A local JDK 21 runtime ran this jar. The jar and JDK are external dependencies,
not embedded in this repository. Rebuilt jars may have different archive
metadata; record the hash actually used on replay.

From `develop/`, run:

```sh
python3 walnut_check.py --java /path/to/java --jar /path/to/Walnut-all.jar
```

The runner creates a fresh session directory on every replay. It imports
only base automata and reconstructs all intermediate quantified relations in
Walnut. It rejects errors even when Walnut returns process exit zero, and
does not reuse old TRUE outputs. The integer meaning of the base automata
still rests on the carry proof; Walnut provides an independent check of
language operations rather than an independent derivation of that invariant.

The generated per-run directories are local runtime evidence. Only the
source runner, pinned version metadata, and final report are distributed.
