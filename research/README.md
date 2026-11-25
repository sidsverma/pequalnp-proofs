# Partial circuit-complexity research

These are checked partial results from two attempts on 25 November 2026. **Neither posted task is solved.** This branch is a public research record, not an upstream proof submission or a claim to project credit.

The base is commit `24cba0a7e1ae4cd6cda51292ac2c28289dfcc387`, with Lean 4.36.0 and the Mathlib revision pinned by `lean/lake-manifest.json`.

## Results

| Source | Result | Remaining gap |
| --- | --- | --- |
| `Lower89.lean` | The specified 45-by-45 cycle-family matrix needs at least 90 gates. | L-meta-10075 requires excluding circuits through 99 gates. |
| `Threshold16.lean` | A 16-gate AND/OR circuit computes threshold-two on seven inputs. Circuits of at least that size have a monotone replacement. | The at-most-15-gate cases of L-meta-10453 remain open. |
| `OneNotObservations.lean` | Two sufficient semantic conditions permit replacing a NOT output by a constant. | These conditions are not established for every circuit in the task. |
| `OneNotCircuitReplacement.lean` | Under those conditions, a circuit-level replacement preserves the function and gate count and uses only AND/OR gates. | This is a conditional helper, not the full replacement statement. |

The circuit-level helpers and the two task-specific results use only `propext`, `Classical.choice`, and `Quot.sound`. All proof files compile without proof placeholders.

`upper104.json` is a separate computational certificate: its circuit was evaluated on all 2,025 promised inputs. Its auxiliary Lean check did not finish, so it is not presented as a checked theorem.

## Reproduce the Lean checks

Install the pinned Lean toolchain and fetch the project's Mathlib cache as described in the root README. From the repository root, run:

```sh
sh research/check-proofs.sh
```

The script compiles the four research modules and prints their axiom dependencies. It does not run the project's contribution checker: these files do not prove the exact posted task statements and are not eligible upstream submissions.

## Search programs

The Python programs require the packages in `requirements.txt`. The C++ programs require a C++17 compiler. Run the searches from this directory; `synth_window.py` reads `threshold16.json`.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python synth_cycle.py 3 19 --seconds 180
.venv/bin/python synth_threshold.py 15 --not 1 --useful-not --seconds 180
.venv/bin/python synth_window.py --min 3 --max 8 --seconds 3
c++ -O3 -std=c++17 search_cycle.cpp -o search_cycle
./search_cycle 3 180
c++ -O3 -std=c++17 search_threshold.cpp -o search_threshold
./search_threshold 15 180 1
```

No full-task counterexample was found. A timeout provides no conclusion. An UNSAT result for a constrained window or fixed-prefix search does not establish a lower bound for all circuits. Any produced witness must be independently evaluated and then checked in Lean before it can support a submission.

All files are under the repository's Apache-2.0 licence.
