/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Definition
public import ReasLib.CategoryTheory.Fibered.InGroupoids

/-!
# Cartesian functors into groupoid fibrations

The target-side groupoid-fibration condition makes preservation of strongly cartesian arrows
automatic for a based functor. This is the raw functor-level input for pseudo-pullback and
full-subbicategory constructions.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory

open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace BasedCategory

/-- The projection stored by `BasedCategory.ofFunctor p` inherits the canonical groupoid-fibred
instance from `p`. -/
@[stacks 02XS "groupoid-fibred projection of a based category"]
instance ofFunctor.projectionInGroupoids
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p] :
    Functor.IsFibered.InGroupoids (BasedCategory.ofFunctor p).p := sorry

end BasedCategory

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- Every based functor into a category fibred in groupoids preserves strongly cartesian
morphisms. Only the target projection needs to be fibred in groupoids; the source projection may
be an arbitrary based category over `C`. -/
theorem PreservesStronglyCartesian.ofTargetInGroupoids
    (G : X ⥤ᵇ Y) [Functor.IsFibered.InGroupoids Y.p] :
    G.PreservesStronglyCartesian := sorry
/- Proof strategy: take a strongly cartesian source arrow. Its image is an arbitrary target
arrow, hence Cartesian by `Functor.IsFibered.InGroupoids.all_isCartesian`; fibredness of `Y.p`
upgrades it canonically to a strongly cartesian arrow. -/

end BasedFunctor

namespace CartesianBasedFunctor

variable {S₁ : Type uX} {S₂ : Type uY}
variable [Category.{vX} S₁] [Category.{vY} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- Regard a based functor with groupoid-fibred target as a cartesian based functor. -/
def ofTargetInGroupoids
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    [Functor.IsFibered.InGroupoids p₂] :
    CartesianBasedFunctor p₁ p₂ :=
  ofBasedFunctor F
    (BasedFunctor.PreservesStronglyCartesian.ofTargetInGroupoids F)

end CartesianBasedFunctor

end CategoryTheory
