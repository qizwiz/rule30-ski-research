# Parenthetical Expressions - OpenCode Integration Test

## Test Instructions

Run these tests in actual OpenCode environment:

```bash
# Navigate to a file and use @explore to verify
cd /path/to/codebase
opencode mcp list
```

## Test Cases

### Test 1: Simple Parenthetical
**Input:** `(thinking-query "spinors")`

**Expected:**
- Parenthetical detected
- RLM tracer called
- Returns trace showing recursive steps
- Final answer displayed

### Test 2: Compose
**Input:** `(compose (thinking-query "spinors") (opencode-search "parse"))`

**Expected:**
- Parenthetical detected
- First step: `thinking-query` called
- Second step: `opencode-search` called with first result
- Combined result returned

### Test 3: Nested Expression
**Input:** `(let [result (thinking-query "spinors")] (+ result 1))`

**Expected:**
- Parenthetical detected
- Let binding works
- Arithmetic executes
- Result returned

### Test 4: Non-Parenthetical
**Input:** `hello world`

**Expected:**
- Not detected as parenthetical
- Treated as regular text
- No MCP calls made

### Test 5: RLM Trace Visibility
**Input:** `(thinking-query "What is RLM?")`

**Expected:**
- RLM tracer shows step-by-step analysis
- Each step appears as RLMTracePart in OpenCode UI
- Summary shows total steps and LLM calls

## What You Should See

### Successful Parenthetical
```
[✓] (thinking-query "spinors")
```

You'll see in OpenCode's reasoning panel:
```
🔄 RLM Step 1: Writing REPL code
   Action: repl_code
   Expression: (llm_query "What is Recursive Language Model?")

🔄 RLM Step 2: Sub-LLM call
   Action: llm_query
   Query: "What makes RLMs different from standard LLMs?"

🔄 RLM Step 3: Final synthesis
   Action: final
   Answer: [Complete answer about RLM differences]
```

### Unsuccessful (No RLM)
```
[!] (thinking-query "invalid server")
```

You'll see:
```
Lisp Error: RLM evaluation not available
```

## Technical Details

- **Parenthetical Detection:** `PAREN_REGEX = /^\(.*\)$/`
- **RLM Tracer:** Port 3010
- **RLM Server:** Port 3001
- **MCP Tool:** `rlm_complete_with_trace`
- **Trace Part Type:** `rlm-trace`
- **OpenCode Part Types:** `lisp`, `rlm-trace`

## Next Steps

1. Open actual OpenCode environment
2. Test parenthetical expressions
3. Verify RLM trace visibility
4. Report results
