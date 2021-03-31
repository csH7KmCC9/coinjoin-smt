# Install prerequisites:
```
pip3 install pysmt
pysmt-install --z3
```

# Set up example CoinJoin amount, taker, inputs, txfees, and cjfees (optional)

Change the global variables prefixed with `example_`. Each party (i.e. participant in the CoinJoin) must be assigned a unique integer ID. `-1` is reserved as a party ID for the party ID of unused outputs.

# Find a good CoinJoin

```
./prototype.py
```

This will first build an SMT problem to encode the CoinJoin constraints with an initial constraint of up to `3 * len(example_inputs)` (i.e. 3 times as many outputs as inputs) CoinJoin outputs and no constraint on the number of outputs not belonging to an anonymity set with at least one other output.

Then, the maximum number of unique outputs is gradually decremented and the problem solved again with the new constraint, until the minimum number of achievable unique outputs is found, subject to the initial constraint on the number of outputs.

Finally, the maximum number of unique outputs is fixed at the discovered minimum and the maximum number of outputs is gradually decremented and the problem solved again with the new constraint, until the minimum number of outputs that allows achieving the minimum number of unique outputs is found.

Note that the choice of `3 * len(example_inputs)` is totally arbitrary here; we could choose more or fewer. The optimization procedure is also arbitrary. There is nothing that says we have to minimize unique outputs at all costs--indeed, since the taker pays the fees but the makers enjoy the privacy benefits, a more judicious tradeoff is probably appropriate. In any case, a binary search is a better procedure than simply decrementing, but that is not implemented here to (hopefully) aid understanding.
