# Recamán's sequence at high altitude

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24554139.svg)](https://doi.org/10.5281/zenodo.24554139)

Clément Chardine. Paper: [`paper/recaman.pdf`](paper/recaman.pdf).

Recamán's sequence ([OEIS A005132](https://oeis.org/A005132)) starts at 0; step `n` subtracts `n` if the result is
non-negative and new, and adds `n` otherwise. This repository holds a paper on its growth, a small Lean formalization, and
two programs that check the paper's explicit words.

## The idea

Let `β` be the number of additions minus the number of subtractions so far. One identity recovers the sequence from it:

    a(m) − a(k) = m (β_m − β_k) − Σ_{k ≤ i < m} (β_i − β_k).

Read at high altitude, where nothing has been visited before, it turns the rule into one about a ±1 walk `u`:

> From height `p + 1`, step **up** iff the walk stood at `p` at some earlier time, and its **mean height since then is
> exactly `p`**. Otherwise step down.

The rule involves neither the size of the numbers nor their position. The paper follows it from the sequence down to a statement about words:

| step | consequence | checked by |
|---|---|---|
| windows of the sequence are plays of a game, whose reach is subadditive | `a(N) ≤ (ρ/2 + o(1)) N²`, `ρ` the reach rate | Lean |
| two values of the reach | `R(13) ≤ 3` by hand: `limsup a(N)/N² ≤ 3/26`; `R(28) ≤ 4` by a small search: `≤ 1/14` | Lean |
| growth is balance | `a(N) = o(N²)` iff subtractions have frequency `1/2` | Lean |
| optimal plays need no opponent | if `ρ > 0`, it is the top speed of stationary walks that obey the rule | paper |
| the dial | `W ≤ cD` on all words gives `ρ ≤ (c−1)/(c+1)`; `c = 2` is proved | Lean |
| **open** | `W ≤ D` on all words. It would give `a(N) = o(N²)` | [OPEN.md](OPEN.md) |

In Lean, `R(13) ≤ 3` is proved by the same search as `R(28) ≤ 4`; the hand proof is in the paper.

## Layout

    paper/            the paper: recaman.tex, recaman.pdf (`make`, with tectonic or latexmk)
    lean/Recaman/     Sequence  the sequence and the identity
                      Game      plays, reach, subadditivity
                      Window    windows of the sequence are plays
                      Growth    from the reach to the growth
                      Balance   growth and the frequency of subtractions
                      Dial      W ≤ 2D, best plays leave the bottom at once, the dial
                      Search    R(13) ≤ 3 and R(28) ≤ 4, with the search and its soundness
                      Main      the results
    tools/game.c      exhaustive checks: reach, dial, ladder
    tools/check.py    checks every explicit word and identity quoted in the paper
    OPEN.md           the open conjecture, and what is known to fail

## Checking

    cd lean && lake exe cache get && lake build     # under two minutes after the download
    lake env lean scripts/Axioms.lean               # only propext, Classical.choice, Quot.sound
    cd .. && python3 tools/check.py

The kernel performs the search itself (`decide +kernel`); there is no `sorry`, `native_decide` or added axiom. The search for
`R(28)` needs about 6 GB of memory.

## Citing

Clément Chardine, *Recamán's sequence at high altitude*, preprint (2026), [doi:10.5281/zenodo.24554139](https://doi.org/10.5281/zenodo.24554139).

## License

The code (`lean/`, `tools/`) is under the Apache License 2.0 ([LICENSE](LICENSE)). The paper (`paper/`) is under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

The paper states how generative AI was used in this work.
