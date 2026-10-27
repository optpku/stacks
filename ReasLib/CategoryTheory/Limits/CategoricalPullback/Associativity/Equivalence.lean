/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Associativity.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# The categorical-pullback reassociation equivalence

Assembly and computation API for the equivalence between the two bracketings of an iterated
categorical pullback.
-/

@[expose] public section

open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]

namespace Limits.CategoricalPullback

variable (F : A ⥤ B) (G : C ⥤ B) (H : C ⥤ D) (I : E ⥤ D)

-- Local declaration justification (source-local notation): this file assembles the fixed
-- endpoints of the explicit reassociation equivalence. The names keep those endpoints readable
-- across its private coherence data and do not define an independent public construction.
local notation "LeftAssociated" => (((π₂ F G) ⋙ H) ⊡ I)
-- Local declaration justification (source-local notation): this is the fixed right-associated
-- endpoint of the same equivalence assembly and has no independent public operation.
local notation "RightAssociated" => (F ⊡ ((π₁ H I) ⋙ G))

namespace Associator

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Naturality of the identity components of the reassociation unit. -/
private theorem associativityUnitNaturality {X Y : LeftAssociated} (f : X ⟶ Y) :
    (𝟭 (CategoricalPullback ((π₂ F G) ⋙ H) I)).map f ≫ (Iso.refl Y).hom =
      (Iso.refl X).hom ≫
        (Associator.forward F G H I ⋙ Associator.inverse F G H I).map f := sorry

/-- The unit isomorphism for categorical-pullback reassociation. -/
private def associativityUnitIso :
    𝟭 (CategoricalPullback ((π₂ F G) ⋙ H) I) ≅
      Associator.forward F G H I ⋙ Associator.inverse F G H I :=
  NatIso.ofComponents (fun X ↦ Iso.refl X) (associativityUnitNaturality F G H I)

/-- Naturality of the identity components of the reassociation counit. -/
private theorem associativityCounitNaturality {X Y : RightAssociated} (f : X ⟶ Y) :
    (Associator.inverse F G H I ⋙ Associator.forward F G H I).map f ≫
        (Iso.refl Y).hom =
      (Iso.refl X).hom ≫
        (𝟭 (CategoricalPullback F ((π₁ H I) ⋙ G))).map f := sorry

/-- The counit isomorphism for categorical-pullback reassociation. -/
private def associativityCounitIso :
    Associator.inverse F G H I ⋙ Associator.forward F G H I ≅
      𝟭 (CategoricalPullback F ((π₁ H I) ⋙ G)) :=
  NatIso.ofComponents (fun X ↦ Iso.refl X) (associativityCounitNaturality F G H I)

/-- The triangle identity for the explicit reassociation unit and counit. -/
private theorem associativityTriangle (X : LeftAssociated) :
    (Associator.forward F G H I).map ((associativityUnitIso F G H I).hom.app X) ≫
        (associativityCounitIso F G H I).hom.app
          ((Associator.forward F G H I).obj X) =
      𝟙 ((Associator.forward F G H I).obj X) := sorry

end Implementation

/-- The canonical equivalence between the two bracketings of an iterated categorical pullback.

```
        F                 G                 H                 I
 A ────────────▶ B ◀──────────── C ────────────▶ D ◀──────────── E
```

For this four-functor zigzag, the explicit forward and inverse functors give a reassociation
equivalence
`(((π₂ F G) ⋙ H) ⊡ I) ≌ F ⊡ ((π₁ H I) ⋙ G)`.

The forward and inverse functors, their object and morphism maps, and both natural isomorphisms
are exposed by the surrounding computation API. -/
@[stacks 02XC "associativity of iterated categorical pullbacks"]
def _root_.CategoryTheory.Limits.CategoricalPullback.associativity :
    LeftAssociated ≌ RightAssociated where
  functor := Associator.forward F G H I
  inverse := Associator.inverse F G H I
  unitIso := Implementation.associativityUnitIso F G H I
  counitIso := Implementation.associativityCounitIso F G H I
  functor_unitIso_comp := Implementation.associativityTriangle F G H I

end Associator

namespace Associator.equivalence

/-- The forward functor of categorical-pullback associativity is the rightward rebracketing
functor. -/
@[simp]
theorem functor :
    (associativity F G H I).functor = Associator.forward F G H I := sorry

/-- The inverse functor of categorical-pullback associativity is the leftward rebracketing
functor. -/
@[simp]
theorem inverse :
    (associativity F G H I).inverse = Associator.inverse F G H I := sorry

/-- The forward component of the reassociation unit is the identity. -/
@[simp]
theorem unitIso.hom.app (X : LeftAssociated) :
    (associativity F G H I).unitIso.hom.app X = 𝟙 X := sorry

/-- The inverse component of the reassociation unit is the identity. -/
@[simp]
theorem unitIso.inv.app (X : LeftAssociated) :
    (associativity F G H I).unitIso.inv.app X = 𝟙 X := sorry

/-- The forward component of the reassociation counit is the identity. -/
@[simp]
theorem counitIso.hom.app (X : RightAssociated) :
    (associativity F G H I).counitIso.hom.app X = 𝟙 X := sorry

/-- The inverse component of the reassociation counit is the identity. -/
@[simp]
theorem counitIso.inv.app (X : RightAssociated) :
    (associativity F G H I).counitIso.inv.app X = 𝟙 X := sorry

end Associator.equivalence

namespace Associator.forward

/-- The forward categorical-pullback reassociation is an equivalence of categories. -/
@[instance]
theorem isEquivalence : (Associator.forward F G H I).IsEquivalence := sorry

end Associator.forward

namespace Associator.inverse

/-- The inverse categorical-pullback reassociation is an equivalence of categories. -/
@[instance]
theorem isEquivalence : (Associator.inverse F G H I).IsEquivalence := sorry

end Associator.inverse

end Limits.CategoricalPullback

end CategoryTheory
