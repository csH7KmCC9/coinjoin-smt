# Install prerequisites
```
pip3 install pysmt
pysmt-install --z3
```

# Set up example CoinJoin amount, taker, inputs, txfees, and cjfees (optional)

Change the global variables prefixed with `example_`. Each party (i.e. participant in the CoinJoin) must be assigned a unique integer ID. `-1` is reserved as a party ID for unused outputs.

# Find a good CoinJoin

```
./prototype.py
```

This will first build an SMT problem to encode the CoinJoin constraints with an initial constraint of up to `3 * len(parties)` (i.e. 3 times as many outputs as there are parties, enough for 1 output in the main CoinJoin amount and 2 change outputs for all parties) CoinJoin outputs and no constraint on the number of outputs not belonging to an anonymity set with at least one other output (i.e. the number of uniquely-identifiable outputs). Then it will solve the problem with an SMT solver and recover the model, or a (set of) variable assignment(s) for which the problem is satisfiable. This tells us how many outputs, which outputs belong to whom, and how many satoshis each output gets.

Then, the constrained maximum number of uniquely-identifiable outputs is gradually decremented and the problem is re-generated and solved again with the new constraint, repeatedly, until the minimum number of uniquely-identifiable outputs that can be achieved using at most `3 * len(parties)` is found.

Finally, the constrained maximum number of uniquely-identifiable outputs is fixed at the discovered minimum and instead the constrained maximum number of outputs (initially `3 * len(parties)`) is decremented, the problem re-generated and solved again with the new constraint, repeatedly, until we discover the minimum number of outputs with which we can achieve the discovered minimum number of uniquely-identifiable outputs.

Note that the choice of `3 * len(parties)` is totally arbitrary here; we could choose more or fewer. The optimization procedure is also arbitrary. There is nothing that says we have to minimize unique outputs at all costs--indeed, since the taker pays most of the fees but the makers enjoy the privacy benefits, a more judicious tradeoff is probably appropriate. In any case, a binary search is a better procedure than simply decrementing, but that is not implemented here to simplify the implementation and (hopefully) aid understanding.
