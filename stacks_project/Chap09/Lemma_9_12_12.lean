module

public import Mathlib.FieldTheory.SeparableDegree
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.12.12:
- primary domain: transitivity of separable field extensions in a tower;
- sampled owner declarations:
  `IsSeparable.tower_top`,
  `Algebra.isSeparable_tower_top_of_isSeparable`,
  `Algebra.IsSeparable`,
  `Algebra.IsSeparable.trans`;
- best owner abstraction: the extension-level owner theorem `Algebra.IsSeparable.trans`;
- primitive data: a tower of field extensions with separability hypotheses on the two stages;
- derived API: the pointwise tower-stability lemmas `IsSeparable.tower_top` and
  `Algebra.isSeparable_tower_top_of_isSeparable`, from which the owner theorem is packaged.

Source/core/bridge triage:
- `source-facing`: separability of the composite extension in a tower `k ⊆ E ⊆ F`;
- `core/canonical`: `Algebra.IsSeparable.trans`;
- `bridge/view`: the pointwise tower-stability lemmas for separable elements.

This file should therefore remain a pure check surface: the source lemma is already exactly the
canonical owner theorem, so any local restatement would only duplicate upstream API. -/

/- Lemma 9.12.12: in a tower of fields `k ⊆ E ⊆ F`, if `E/k` and `F/E` are separable field
extensions, then `F/k` is also a separable field extension; this is the canonical transitivity
theorem `Algebra.IsSeparable.trans`. -/
@[stacks 09HB]
#check Algebra.IsSeparable.trans
