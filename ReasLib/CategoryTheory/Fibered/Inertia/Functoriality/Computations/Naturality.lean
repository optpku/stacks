/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Computations.Action.Objects
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Computations.Action.TwoCell
import Mathlib.Tactic.CrossRefAttribute

/-!
# Section and forgetful naturality for the based-inertia pseudofunctor

This leaf exposes the `1`- and `2`-cell transport equations for forgetting automorphisms and
for inserting identity automorphisms.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

namespace Inertia

/-- The ordinary based-inertia pseudofunctor commutes with forgetting the selected
automorphism. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor forgetful naturality"]
theorem pseudofunctor.forget.naturality
    {X Y : BasedCategory.{v₁, u₁} C} (F : X ⥤ᵇ Y) :
    (pseudofunctor C).map F ⋙ forget Y =
      forget X ⋙ (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)).map F := sorry

/-- Forgetting the selected automorphism is `2`-natural for the ordinary based-inertia
pseudofunctor. -/
@[stacks 04Z4 "based inertia pseudofunctor forgetful two-naturality"]
theorem pseudofunctor.forget.naturality₂
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y} (η : F ⟶ G) :
    BasedCategory.whiskerRight ((pseudofunctor C).map₂ η) (forget Y) =
      eqToHom (pseudofunctor.forget.naturality F) ≫
        BasedCategory.whiskerLeft (forget X)
          ((Pseudofunctor.id (BasedCategory.{v₁, u₁} C)).map₂ η) ≫
          eqToHom (pseudofunctor.forget.naturality G).symm := sorry

/-- The identity pseudofunctor map followed by the neutral section agrees with first taking
the neutral section and then applying ordinary based inertia. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor neutral-section naturality"]
theorem pseudofunctor.identitySection.naturality
    {X Y : BasedCategory.{v₁, u₁} C} (F : X ⥤ᵇ Y) :
    (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)).map F ⋙ identitySection Y =
      identitySection X ⋙ (pseudofunctor C).map F := sorry

/-- The identity-automorphism section is `2`-natural for the ordinary based-inertia
pseudofunctor. -/
@[stacks 04Z4 "based inertia pseudofunctor neutral-section two-naturality"]
theorem pseudofunctor.identitySection.naturality₂
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y} (η : F ⟶ G) :
    BasedCategory.whiskerLeft (identitySection X) ((pseudofunctor C).map₂ η) =
      eqToHom (pseudofunctor.identitySection.naturality F).symm ≫
        BasedCategory.whiskerRight
          ((Pseudofunctor.id (BasedCategory.{v₁, u₁} C)).map₂ η)
          (identitySection Y) ≫
          eqToHom (pseudofunctor.identitySection.naturality G) := sorry

end Inertia

end BasedCategory
end CategoryTheory
