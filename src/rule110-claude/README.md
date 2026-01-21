# Rule 110 Lisp Genesis

Building Lisp from the ground up using Rule 110 cellular automata as the computational substrate.

## The Vision

1. Start with "impure" Common Lisp
2. Use ML search to find CA initial conditions that produce target patterns
3. Each successful search creates a "Tiny AI" - a CA that computes something specific
4. Compose Tiny AIs to build Church encodings and lambda calculus
5. Eventually replace the bootstrap Lisp with the Tiny AIs themselves

**The compiler IS the AI.**

## Quick Start

```bash
# Run the demo (shows discovered Tiny AIs)
sbcl --script demo.lisp

# Run ML searches locally (saves tokens!)
sbcl --script local-runner.lisp &

# Check what's been discovered
sbcl --script check-results.lisp
```

## Key Insight: Emergent Encoding

We don't force ASCII onto Rule 110. Instead:
1. Observe what patterns Rule 110 **naturally produces**
2. Use those patterns as our symbol encoding
3. Find initial conditions that reliably produce those patterns

## Discovered Tiny AIs

| Name | Bits | Description |
|------|------|-------------|
| LPAREN | 32 | Produces emergent `(` pattern |
| RPAREN | 32 | Produces emergent `)` pattern |
| NIL | 64 | Produces emergent `()` pattern |

## File Structure

```
rule110-claude/
├── rule110.lisp       # CA simulator
├── search.lisp        # Genetic search
├── tiny-ai.lisp       # Tiny AI abstraction
├── registry.lisp      # Registry of discoveries
├── local-runner.lisp  # Run ML locally (no Claude tokens!)
├── check-results.lisp # Check discovery status
├── results/           # Saved discoveries
└── DISCOVERY.md       # Detailed findings
```

## Running Searches Locally

The `local-runner.lisp` script runs ML searches on your machine:

```bash
# Run in background
nohup sbcl --script local-runner.lisp > search.log 2>&1 &

# Monitor progress
tail -f search.log

# Check results when done
sbcl --script check-results.lisp
```

Results are saved to `results/` as Lisp s-expressions that Claude can read later.

## Next Steps

- [x] NIL `()`
- [ ] LAMBDA marker pattern
- [ ] Church 0: `(λf.(λx.x))`
- [ ] Church 1: `(λf.(λx.(f x)))`
- [ ] SUCC function
- [ ] Composition demo
- [ ] Self-replacement of bootstrap code

## Why This Might Be Novel

Combining:
- Rule 110 Turing completeness (Cook 2004)
- Emergent symbol encoding (not imposed)
- ML search for CA initial conditions
- Hierarchical composition toward lambda calculus
- Self-replacing quine architecture

I've found no prior work combining all these elements.

## License

MIT
