# Solved conjectures

Machine-checked proofs of open conjectures, starting with graceful labelings of trees. Every result comes with a Lean 4 formalization, an executable check, and a written proof.

**Alpar Garib** · built with a **Claude × GPT-6.2 Astra** combination

## Results

| # | Conjecture | Result | Lean |
| :-: | :--- | :--- | :-: |
| 1 | [Rofa's 0-rotatability conjecture for symmetric spiders](results/symmetric-spiders/) | Proved for every leg length $L \ge 5$. With the known cases $L \le 4$, every symmetric spider is 0-rotatable. | ✅ |

✅ means the main theorem is fully checked by Lean, with no `sorry` and no axioms beyond Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`).

## Check it yourself

You need [elan](https://github.com/leanprover/elan) (the Lean installer) and Python 3.

```sh
lake exe cache get          # download prebuilt Mathlib
lake build                  # checks every proof
lake env lean Audit.lean    # prints the main statements and the axioms they use
python3 results/symmetric-spiders/scripts/verify.py 200 --general-through 14
python3 results/symmetric-spiders/scripts/check_lean_construction.py
```

The same Lean build runs automatically on every push (see the Actions tab).

## Credits

Alpar Garib, together with Claude (Anthropic) and GPT-6.2 Astra (OpenAI).

If you spot a gap or know of earlier work covering any result here, please open an issue.

## License

Apache-2.0
