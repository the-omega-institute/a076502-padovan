# Computations and formal proofs

The [manuscript](../manuscript/output/pdf/paper.pdf) gives the mathematical
argument. This directory supplies the exact computations and formal proofs.
Run the commands below from this directory with Python 3, using only its
standard library.

| Command | Result |
| --- | --- |
| `python3 automata_proof.py --bound 8` | Constructs the finite-state relations and verifies the recurrence and first differences by exhaustive inclusion checks. |
| `python3 discrepancy_certificate.py` | Produces an exact rational discrepancy certificate. |
| `python3 morphic_certificate.py` | Constructs the explicit non-erasing morphic presentation and checks its finite structural conditions. |
| `python3 extrema_certificate.py` | Computes refined rational extrema enclosures and witness representations. |
| `python3 paper_checks.py` | Replays the independent verifier, compares small suffix searches, and checks the saved witnesses. |
| `python3 independent_checks.py --limit 1000000` | Optional finite-prefix diagnostic. |

Generated automata and reports are in `automata-results/`. The last command
is a finite diagnostic; the all-index argument uses the invariant and
language-inclusion certificates described in the paper.

The original correction tables and independent verifier are Benoit Cloitre's
programs in `../correspondence/attachments/`, preserved byte-for-byte.
The package's automata transformations and verification implementations are
separate from his independent verifier.

See [lean/README.md](lean/README.md) for the theorem scope and formal build,
and [walnut/README.md](walnut/README.md) for the independent Walnut replay.
The existing isolated build reports are under `ci-results/`; their recorded
source hashes identify the exact Lean development checked.
