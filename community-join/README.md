Community Join
----
This is a repo for the solver for community joins. These are CoinJoins that are executed manually by people communicating PSBTs over GPG-encrypted emails (or some other out-of-scope communication channel).

These are a bit different from regular CoinJoins:
- There is no maker/taker model. All parties are takers, and there is one coordinator who knows the association between parties' inputs and outputs and may or may not be party to a given join.
- Parties provide the following values to the coordinator:
    - party\_inputs: A list of UTXOs (`txid:index`) the party wishes to join.
    - max\_txfee\_contribution: How many satoshis that party is willing to contribute to the CoinJoin transaction fee. Must be at least `500 * len(party_inputs)`. Will be scaled in proportion to the number of inputs actually used (so if you offer 3 inputs with a max contribution of 1500 satoshis, and only 2 of your inputs are chosen for the CoinJoin, you won't pay more than 1000 satoshis).
    - party\_output\_addrs: A list of `3 * len(party_inputs)` bech32 SegWit addresses that party is willing to receive coins on.
- The coordinator runs this script on the parties' values above and gets a solution selecting some of the parties' offered inputs and sending their satoshis to some of the parties' provided addresses. The coordinator builds a PSBT template for the parties to sign. The coordinator provides this PSBT template to all the parties along with a deadline for them to respond.
- Each party verifies their constraints are satisfied (they're not losing more than proportionally scaled max\_txfee\_satoshis and their outputs are not uniquely-identifiable). If so, they sign their inputs and communicate this back to the coordinator.
- The coordinator waits until all parties have responded or the deadline expires. If the deadline expires, the CoinJoin fails and the UTXOs corresponding to the non-responsive parties may be banned from future joins. Once all parties have responded the CoinJoin transacted is fully signed and broadcast and the CoinJoin is complete.
