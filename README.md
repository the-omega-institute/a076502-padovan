# A076502: a Padovan-automatic nested recurrence

Reproducibility materials for **A Padovan-automatic description of a nested
recurrence**, by **Benoit Cloitre, Haobo Ma, and Wenlin Zhang**.

The paper identifies OEIS A076502 using greedy Padovan representations and
finite automata. It proves the exact floor-offset set `{-1, 0, 1, 2}`, a
uniform discrepancy bound, an explicit 26-letter non-erasing morphic
presentation, and least balance constant 4. The repository includes the
mathematical manuscript, exact computational certificates, and Lean proofs.

- [Read the manuscript](manuscript/output/pdf/paper.pdf).
- [Compile the LaTeX source](manuscript/BUILD.md).
- [Inspect the formal theorem scope](develop/lean/README.md).
- [Browse versioned releases](https://github.com/the-omega-institute/a076502-padovan/releases).

## Run the computational checks

Clone this repository, then run with Python 3 (standard library only):

```sh
cd develop
python3 paper_checks.py
```

This replays Benoit Cloitre's independently written verifier at carry bounds
8 and 10, compares exact suffix optimization with exhaustive enumeration at
lengths 5, 8 and 12, and checks all eight stored extrema witnesses.
Reports are written to `develop/automata-results/`.

To regenerate the main automata and certificates, run from `develop/`:

```sh
python3 automata_proof.py --bound 8
python3 discrepancy_certificate.py
python3 morphic_certificate.py
python3 extrema_certificate.py
```

The [computation guide](develop/README.md) describes the remaining commands.
The two original author-supplied Python programs retain their historical
paths under `correspondence/attachments/`, which the verification code uses.
That directory contains only those programs.

## Rebuild the Lean proofs

The development pins Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. Install Elan, Git and Python 3,
then run from the repository root on a machine with sufficient memory and
network access:

```sh
python3 develop/clean_ci.py
```

The command creates a fresh temporary Lake project, fetches the pinned
dependencies and official Mathlib binary cache, and rebuilds the complete
local proof closure. It records source hashes, command results, and final
theorem axiom closures in `develop/ci-results/`. It does not require this
repository to be hosted on GitHub or a hosted CI service to be available.

The archived September 23, 2026 build passed **69 Lean modules and 18 final
theorem axiom audits**. Its source hashes match the distributed Lean files.
These are records of that isolated build, not a new run performed when the
repository was published. Final theorem closures use only `propext`,
`Classical.choice`, and `Quot.sound`.

The formalization includes the recurrence identification, exact offset set,
six-decimal discrepancy bound, concrete morphic identity, exact balance 4,
and an effective extrema algorithm. The finer K=200 numerical enclosures
come from separate exact rational computations. The original six-letter
identity remains open.

## Walnut

The [Walnut guide](develop/walnut/README.md) records the pinned Walnut version
and the replay command. Java and the Walnut jar are external dependencies.
The archived report records six quantified checks returning `TRUE`.

## Authors and citation

Authors are listed alphabetically:

- Benoit Cloitre.
- Haobo Ma, ChronoAI Pte Ltd; The Omega Institute.
- Wenlin Zhang, National University of Singapore; The Omega Institute.

Use [CITATION.cff](CITATION.cff) for repository citation metadata. The paper
contains the contribution and AI-use statements. This is a joint paper's
artifact repository maintained under The Omega Institute. Related work and
reusable results are developed in [trureturing](https://github.com/the-omega-institute/trureturing).
See [RIGHTS.md](RIGHTS.md) for the current rights statement.

## Archive and integrity

A Zenodo DOI will be added after the GitHub integration is enabled and the
first release is archived. Repository publication alone does not create a DOI.

`SHA256SUMS.json` records the distributed file hashes. Check them before
running programs that regenerate reports:

```sh
python3 - <<'PY'
import hashlib, json
from pathlib import Path
for name, expected in json.loads(Path('SHA256SUMS.json').read_text()).items():
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == expected, name
print('All distributed file hashes match.')
PY
```
