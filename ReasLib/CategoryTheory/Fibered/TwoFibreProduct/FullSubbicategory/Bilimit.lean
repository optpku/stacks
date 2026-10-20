/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Bilimit

/-!
# Bilimit cone for explicit two-fibre products

The chosen pseudo-pullback cone and its bilimit certificate in a full subbicategory.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X Y S : P.FullSubbicategory}

/-- The canonical pseudo-pullback cone in a property-selected full subbicategory.

For `P₀ := apex F G`, the diagram is read as

```text
                              fst F G
           P₀ ─────────────────────────────▶ X
            │                                 │
    snd F G │           comparison ⇓          │ F
            │                                 │
            ▼                                 ▼
            Y ───────────────────────────────▶ S
                               G
```

The invertible cell `comparisonIso F G` identifies the route across the top and down the right
with the route down the left and across the bottom. -/
@[stacks 02XQ "canonical cone of a full-subbicategory two-fibre product"]
noncomputable def cone (F : X ⟶ S) (G : Y ⟶ S) : PseudoPullbackCone F G where
  pt := apex F G
  fst := fst F G
  snd := snd F G
  iso := comparisonIso F G

/-- The apex of the canonical full-subbicategory cone is the explicit two-fibre-product
owner. -/
@[simp]
theorem cone.pt (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).pt = apex F G := sorry

/-- The first leg of the canonical full-subbicategory cone is its first projection. -/
@[simp]
theorem cone.fst (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).fst = fst F G := sorry

/-- The second leg of the canonical full-subbicategory cone is its second projection. -/
@[simp]
theorem cone.snd (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).snd = snd F G := sorry

/-- The structural cell of the canonical full-subbicategory cone is its explicit comparison
isomorphism. -/
@[simp]
theorem cone.iso (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).iso = comparisonIso F G := sorry

/-- The explicit cone remains a bilimit after restricting to any full subbicategory whose object
property is closed under the chosen based pseudo-pullback. This is a named instance because
generic universal-lift constructions take the bilimit certificate as a typeclass argument. -/
@[stacks 0041 "(2)", stacks 0047 "(2)", stacks 04SB "(2)"]
instance cone.isBilimit (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).IsBilimit := sorry
/- Proof strategy: identify `cone F G` with
`Bicategory.PseudoPullbackCone.inFull P
  (BasedCategory.PseudoPullback.cone F.hom G.hom) _`, then apply
`Bicategory.PseudoPullbackCone.inFull.isBilimit` and
`BasedCategory.PseudoPullback.cone.isBilimit`. -/

end TwoFibreProduct

end CategoryTheory
