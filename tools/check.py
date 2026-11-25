#!/usr/bin/env python3
"""Check every explicit word quoted in the paper, and its identities on the sequence.  Standard library only."""

def walk(word):
    u = [0]
    for c in word:
        u.append(u[-1] + (1 if c == "+" else -1))
    return u

def witnesses(u, t):
    return [s for s in range(t) if u[s] == u[t] - 1 and sum(u[i] - u[s] for i in range(s, t)) == -1]

def legal(word):
    u = walk(word)
    return all(u[t] < 2 or (word[t] == "+") == bool(witnesses(u, t)) for t in range(len(word)))

def counts(word, far=1):
    """(W, D), where W counts the witnessed up-steps all of whose witnesses are at distance at least `far`."""
    u = walk(word)
    W = 0
    for t, c in enumerate(word):
        if c == "+":
            w = witnesses(u, t)
            W += bool(w) and t - max(w) >= far
    return W, word.count("-")

# Table 1: plays that first reach height H at time T
PLAYS = {
    2: "++",
    3: "+-+++",
    4: "++-+---+++-+++",
    5: "++-+-+----+++-+++---+++-+-+++",
    6: "++----++-+++-+-+-+-+-+-+--+++--+++-+-+-+++",
    7: "++----+++---+++---+++--+++---++-+++-+--+++---+++---+++--+++-+-+-+++",
}
for H, p in PLAYS.items():
    u = walk(p)
    assert legal(p) and u[-1] == H and max(u[:-1]) == H - 1
    print(f"height {H} at time {len(p)}")

# Section 7.1: the conjecture is sharp on the two blocks and on all their concatenations of at most 8 blocks
from itertools import product

def fast_counts(word):
    u, A = walk(word), [0]
    for x in u:
        A.append(A[-1] + x)
    W = sum(c == "+" and any(u[s] == u[t] - 1 and A[t] - A[s] == u[s] * (t - s) - 1 for s in range(t))
            for t, c in enumerate(word))
    return W, word.count("-")

for k in range(1, 9):
    for blocks in product(("-+++", "--++++-+++"), repeat=k):
        W, D = fast_counts("".join(blocks))
        assert W == D
print("sharp blocks: W = D on all 510 concatenations of at most 8 blocks")

# Section 8, row by row: two up-steps from height 2, one down-step from height 1
p = "++-+-+-+-+-+---++++-+"
u = walk(p)
assert legal(p)
assert sum(u[t] == 2 and p[t] == "+" for t in range(len(p))) == 2
assert sum(u[t] == 1 and p[t] == "-" for t in range(len(p))) == 1
print("(1) no charging row by row")

# Section 8, return to the bottom: reaches 4 without going below 1 after its first visit to 2
p = "+--+++-+-+-+++"
u = walk(p)
assert legal(p) and u[-1] == 4 and min(u[u.index(2):]) >= 1
print("(2) early dips are stored")

# Section 8, short and long: too many far witnesses
LONG = (
    "--+-+-+---++++++--+-+----+-++++-+-+----+-++++-+-+++--+-+-+-+-+----+++++-+-+--+-+----+++++-+-+++--"
    "-++-+-+-+---+-++++---++-+++-+-++--+-+-+-+----+++++--++-+-+-+-+++-+--++---+----++++++--+-++--++-++"
)
W, D = counts(LONG, far=11)
assert (len(LONG), W, D) == (194, 49, 92) and counts(LONG)[0] <= D
print("(3) far witnesses: 49 > 92 / 2")

# the master identity and the layer form of the rule, on the first terms of the sequence
N = 400
a, beta, seen = [0], [0], {0}
for n in range(1, N):
    down = a[-1] >= n and a[-1] - n not in seen
    a.append(a[-1] - n if down else a[-1] + n)
    beta.append(beta[-1] + (-1 if down else 1))
    seen.add(a[-1])
for m in range(N - 1):
    layers = [beta[m] - beta[k] - 1 for k in range(m)
              if sum(beta[i] - beta[k] for i in range(k, m)) == m * (beta[m] - beta[k] - 1) - 1]
    assert all(a[m] - a[k] == m * (beta[m] - beta[k]) - sum(beta[i] - beta[k] for i in range(k, m)) for k in range(m))
    assert (beta[m + 1] > beta[m]) == (a[m] < m + 1 or bool(layers))
print("identities hold on the first", N, "terms")
