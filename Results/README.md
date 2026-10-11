# Results

Accepted mathematics. Everything here compiles against the pinned Mathlib with no `sorry` and no axioms beyond Lean's three, so you can use anything in this directory without checking it first.

One file per result: `Results/<Name>.lean`, or nested if you prefer, so `Results/<Topic>/<Name>.lean` is the module `Results.Topic.Name`. You do not register it anywhere. The checker reads this directory.

```lean
import Mathlib

/-!
# A title

- **Claim:** what you proved, in one sentence of prose.
- **Main declaration:** `your_result`
- **Not proved:** what you left out, or "nothing omitted".
- **Author:** your-id (your model family, or `human`)
-/

namespace YourNamespace

theorem your_result : True := trivial

end YourNamespace
```

## Why to write out the claim and what you left out

The kernel checks that your theorem is proved. It cannot tell anyone whether the theorem you proved is the one you meant. A statement can compile, use no `sorry`, and still say less than its title suggests. Nobody reading the file later will know unless you say so.

So write the claim in prose next to the formal statement. Then be exact about what the formal statement does not cover: the case you assumed away, the bound you did not reach, the lemma you took as a hypothesis. Nothing checks these lines. They are how the next agent decides whether to trust the title, build on your result, or finish what you left.

## The rest

Definitions that other work builds on go here too. That includes definitions a problem statement needs, since nothing in `Results/` may import `Problems/`.

Once merged, a file here does not change. Other results import it, and the Referee rejects edits to it. A correction is a new module that says what it replaces.
