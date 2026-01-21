# Rule 110 Lisp Genesis - Discovery Log

## Date: 2026-01-21

## The Breakthrough

We discovered that forcing ASCII encoding onto Rule 110 doesn't work - the CA simply cannot produce arbitrary bit patterns from any initial condition. This was proven by exhaustive search of all 65,536 possible 16-bit initial states.

Instead, we let the encoding **emerge** from Rule 110's natural dynamics.

## Emergent Encoding

Rule 110 has natural attractors - patterns it "wants" to produce. By sampling 10,000 random initial conditions and observing outputs after 40 generations, we found the most common stable patterns:

| Symbol | Emergent Bit Pattern     | Description |
|--------|--------------------------|-------------|
| `(`    | `1100110001001101`       | Most common 16-bit pattern |
| `)`    | `0001111100010011`       | Second most common |
| `NIL`  | `11001100010011010001111100010011` | Concatenation of ( and ) |

## Discovered Tiny AIs

Each "Tiny AI" is a Rule 110 cellular automaton with specific initial conditions that produces a target emergent pattern.

### LPAREN Tiny AI
- **Initial State (32 bits):** `11101110000110001001011001010110`
- **CA Generations:** 40
- **Output Position:** 11
- **Target Pattern:** `1100110001001101`

### RPAREN Tiny AI
- **Initial State (32 bits):** `01000111011010100101000100100001`
- **CA Generations:** 40
- **Output Position:** 4
- **Target Pattern:** `0001111100010011`

### NIL Tiny AI
- **Initial State (64 bits):** `0100110011011101110100100010010100100110111101010011001100101011`
- **CA Generations:** 50
- **Output Position:** 24
- **Target Pattern:** `11001100010011010001111100010011`

## Key Insight

The encoding is not imposed but **discovered**. We find what Rule 110 naturally produces, then find initial conditions that reliably produce those patterns. This is closer to the user's vision: the computational substrate defines its own symbols.

## Implications

1. **Church encodings will use emergent patterns** - not ASCII
2. **Composition becomes meaningful** - NIL is genuinely "()" in the emergent encoding
3. **The quine closure is achievable** - we can replace bootstrap code with discovered CAs
4. **This appears to be novel** - I've found no prior work combining:
   - Rule 110 Turing completeness
   - Emergent symbol encoding
   - ML search for initial conditions
   - Hierarchical composition toward lambda calculus

## Next Steps

1. Find emergent pattern for `lambda`
2. Find Church numeral 0: `(λf.(λx.x))`
3. Find SUCC function
4. Demonstrate composition
5. Begin self-replacement of bootstrap code

## Verification

All discoveries were verified by:
1. Running the CA with discovered initial conditions
2. Checking all windows in output for exact pattern match
3. Confirming position and completeness of match
