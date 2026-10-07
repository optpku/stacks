module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Co-Grothendieck projections of strict groupoid presheaves

The strict-functor specialization of the generic pointwise-groupoidal API.
-/

@[expose] public section

universe w v₁ v₂ u

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Opposite

variable {𝒞 : Type u} [Category.{v₁} 𝒞]

/- A strict presheaf of groupoids first passes through `Grpd.forgetToCat` and then through
`Functor.toPseudofunctor'`. Mathlib already owns its objects `(U, x)`, arrows `(f, φ)`,
composition, and projection through the co-Grothendieck construction. -/

/-- The canonical projection `p_F : 𝒮_F ⥤ 𝒞` associated to a presheaf of groupoids:

```text
 𝒮_F = ∫ᶜ ((F ⋙ Grpd.forgetToCat).toPseudofunctor') ───────── p_F ─────────▶ 𝒞
```

It exposes the canonical total category directly rather than through another alias. -/
def groupoidPresheafProjection (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) :
    (∫ᶜ ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) ⥤ 𝒞 :=
  forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')

namespace groupoidPresheafProjection

/-- Example 4.37.1 (Stacks 0049): the canonical projection associated to a strict presheaf of groupoids is fibred in
groupoids. -/
@[stacks 0049 "groupoid presheaf projection is fibred in groupoids"]
instance inGroupoids
    (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) :
    Functor.IsFibered.InGroupoids (groupoidPresheafProjection F) := sorry

end groupoidPresheafProjection

end CategoryTheory.Pseudofunctor.CoGrothendieck
