/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Galois.Notation
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Definition 9.21.3:
- primary domain: Galois extensions and their automorphism groups in field theory;
- sampled chapter/project owner declarations:
  `Gal(E / F)`,
  `(inferInstance : Group Gal(E / F))`,
  `IsGalois`,
  `IsGalois.card_aut_eq_finrank`;
- best owner abstraction: the canonical automorphism-group owner is `Gal(E / F)`, with
  `IsGalois F E` as the extension property naming the case in which this automorphism group is
  called the Galois group.

Layer triage:
- `source-facing`: the terminology that for a Galois extension `E/F`, the automorphism group of
  `E` over `F` is called the Galois group;
- `core/canonical`: `Gal(E / F)`;
- `bridge/view`: later owner theorems for Galois extensions, such as
  `IsGalois.card_aut_eq_finrank`.

Primitive data are only the field extension `E/F` and its `F`-algebra structure. The source's
extra `IsGalois` hypothesis does not create a new object; it only specifies the terminology for
the already canonical owner `Gal(E / F)`. So this file should remain a direct check/check surface
rather than introduce any parallel local alias or wrapper.
-/

/- Definition 9.21.3 (Tag 09DV): when `E/F` is a Galois extension, its Galois group is the
already existing canonical automorphism group `Gal(E / F)`. -/
@[stacks 09DV]
#check Gal(E / F)

/- Companion check: the Galois group uses the canonical group structure on `Gal(E / F)` induced by
composition. -/
#check (inferInstance : Group Gal(E / F))

end
