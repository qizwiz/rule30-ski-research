# Rule 110 Lisp Genesis - Architecture

## What We Built

A system that builds computation from the ground up using Rule 110 cellular automata, culminating in universal computation via SKI combinators.

```
┌─────────────────────────────────────────────────────────────────┐
│  LEVEL 4: Bootstrap Lisp (OPTIONAL - convenience interface)    │
├─────────────────────────────────────────────────────────────────┤
│  LEVEL 3: SKI Combinators - universal computation              │
│           S K K = I (verified)                                  │
│           ANY computable function expressible                   │
├─────────────────────────────────────────────────────────────────┤
│  LEVEL 2: Composition & SUCC - transforms on tiny AIs          │
│           wire(), compose-sequential()                          │
│           SUCC = meta-transform (n → n+1)                       │
├─────────────────────────────────────────────────────────────────┤
│  LEVEL 1: Tiny AIs - CAs that produce emergent patterns        │
│           LPAREN, RPAREN, NIL, LAMBDA, CHURCH-0, CHURCH-1      │
├─────────────────────────────────────────────────────────────────┤
│  LEVEL 0: Rule 110 - Turing-complete substrate                 │
└─────────────────────────────────────────────────────────────────┘
```

## Key Insight: Emergent Encoding

We don't force encodings onto Rule 110. We discover what patterns it naturally produces, then use those as symbols.

| Symbol | Emergent Pattern | Bits |
|--------|-----------------|------|
| `(`    | `1100110001001101` | 16 |
| `)`    | `0001111100010011` | 16 |
| NIL    | lparen + rparen | 32 |
| LAMBDA | discovered 32-bit pattern | 32 |
| CHURCH-0 | discovered 48-bit pattern | 48 |
| CHURCH-1 | discovered 64-bit pattern | 64 |

## Files

```
rule110-claude/
├── rule110.lisp        # The CA simulator
├── search.lisp         # Genetic search for initial conditions
├── tiny-ai.lisp        # Tiny AI abstraction
├── registry.lisp       # Registry of discovered tiny AIs
├── compose.lisp        # Composition layer (wiring)
├── ski.lisp            # S, K, I combinators
├── local-runner.lisp   # ML search (runs locally, saves tokens)
├── status.sh           # Quick status check
├── watcher.sh          # Background status updater
├── results/            # Discovered tiny AIs saved here
│   ├── lambda.lisp
│   ├── church-zero.lisp
│   └── church-one.lisp
├── DISCOVERY.md        # Discovery log
└── ARCHITECTURE.md     # This file
```

## The Path to Full Replacement

### Currently Replaceable
- **Pattern generation**: Any Lisp code that outputs `()`, `(`, `)` can use tiny AIs instead
- **Church numerals**: 0 and 1 are tiny AIs; any number via SUCC composition
- **Any SKI-expressible function**: which is ALL computable functions

### Still Bootstrap (for now)
- The genetic search algorithm
- The composition wiring logic
- The REPL interface

### Full Quine Closure (future)
When the search algorithm itself is expressed as SKI composition of tiny AIs, the system becomes fully self-sufficient. The bootstrap Lisp becomes vestigial.

## Novel Contributions

1. **Emergent encoding** - letting the CA define its own symbols
2. **ML search for CA initial conditions** - finding patterns reliably
3. **Composition as computation** - wiring CAs together
4. **SKI on tiny AIs** - universal computation via CA composition
5. **Incremental replacement architecture** - bootstrap → pure CA

## Verification

All claims verified by running actual CAs:
- Tiny AIs produce exact bit patterns ✓
- Composition wiring works ✓
- Church numerals apply f correct number of times ✓
- SUCC transforms n to n+1 ✓
- S K K = I identity holds ✓

## What This Means

Any computation can be expressed as:
1. A composition of Rule 110 CAs
2. With learned initial conditions
3. Wired together via SKI combinators

The "compiler" is the AI (the search that finds initial conditions).
The "runtime" is Rule 110.
The "program" is the wiring.
