# The witness–descent conjecture

Everything below is elementary and self-contained.

A **word** is a finite string of `+` and `-`. It describes a walk `u_0 = 0, u_1, u_2, …` by steps of `±1`. A time `s < t`
**witnesses** step `t` (the step from `u_t` to `u_{t+1}`) if

    u_t = u_s + 1     and     Σ_{s ≤ i < t} (u_i − u_s) = −1.

Equivalently, the mean of `u` over `(s, t]` is exactly `u_s`, and the walk ends one above it. Let `W` be the number of up-steps
that have a witness, and `D` the number of down-steps.

> **Conjecture.** `W ≤ D` for every word.

**What it gives.** `a(N) = o(N²)` for Recamán's sequence, and frequency `1/2` for its subtractions. More generally `W ≤ cD` gives
`limsup a(N)/N² ≤ (c−1)/(2(c+1))` (Lean: `growth_of_dial`).

**Milestones.** `c = 2` is a theorem. Any `c < 2` is new; `c < 8/5` beats the paper's hand bound `3/26`; `c < 4/3` beats `1/14`.

## Known

- Sharp: `-+++` and `--++++-+++` have `W = D`, as do all their concatenations of at most 8 blocks (`tools/check.py`).
- No slack: `W ≤ cD + o(length)` is equivalent to `W ≤ cD`. A proof of `c = 1` must be exact.
- True if no two down-steps are consecutive: the first step of a witness window pays for it.
- The ladder: let `W_K` count only witnesses at distance `≤ K`. If `W_K ≤ D` for each `K`, the conclusions follow. Each rung is a
  question about positive cycles in a graph on `2^K` states. Rungs `K ≤ 28` hold (`tools/game rung 28`, measured).
- Holds on all words of length `≤ 30` (`tools/game dial 30`, measured).
- Between two down-steps nothing happens but climbing. If `p_1, …, p_D` are the heights the down-steps depart from, then run `j` of
  up-steps can witness only one step of run `k`, only for `k − j` odd, and only at the height `r` with `Σ_{j<i≤k} p_i = (k−j) r + (k−j−1)/2`.

## Known to fail

| idea | refuted by |
|---|---|
| charge up-steps from height `q` to down-steps from `q − 1` | `++-+-+-+-+-+---++++-+`: two against one |
| each new record needs a return to the bottom | `+--+++-+-+-+++`: an early dip is spent late |
| witnesses at distance `≥ 11` number at most `D/2` | a 194-step word with 49 against 92 (`tools/check.py`) |
| an approximate version | no slack, above |

The third statement holds on all words of length `≤ 30` (`tools/game dial 30`). Before building on a lemma, try to break it on
long words built by search, as well as on all short ones.

## Checking a claim

A refutation of the conjecture is a single word; `counts` in `tools/check.py` computes its `W` and `D`.
