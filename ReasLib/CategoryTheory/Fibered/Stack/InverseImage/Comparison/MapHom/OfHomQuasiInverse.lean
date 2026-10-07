module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.Pullback
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse-image action from an explicit Hom quasi-inverse

This file gives the alternate presentation of inverse image on morphisms for
consumers that already have a quasi-inverse of the canonical forward Hom
functor.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage

variable {u : C ⥤ D}

/-- The functor on stack-morphism categories induced by inverse-image constructions and an
explicit quasi-inverse of the canonical Hom functor. This is the alternate Hom-equivalence
presentation; the direct stackification presentation is `mapHom`. -/
@[stacks 04WS "inverse-image morphisms from a Hom quasi-inverse"]
noncomputable def mapHom.ofHomQuasiInverse
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [u.IsContinuous J K]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (homFunctor I I'.target)) :
    (S ⟶ S') ⥤ (I.target ⟶ I'.target) :=
  (q.liftFunctor (S ⟶ S')).obj
    (postcomp S (pullbackComparison I'))

namespace mapHom.ofHomQuasiInverse

/-- The Hom-lift presentation applies the supplied inverse functor to postcomposition with the
canonical pullback comparison. -/
@[stacks 04WS "object action of a Hom quasi-inverse presentation", simp]
theorem obj
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [u.IsContinuous J K]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (mapHom.ofHomQuasiInverse I I' q).obj F =
      q.inverse.obj (F ≫ pullbackComparison I') := sorry

/-- The Hom-lift presentation sends a stack `2`-cell by right whiskering with the canonical
pullback comparison and applying the supplied inverse functor. -/
@[stacks 04WS "2-cell action of a Hom quasi-inverse presentation", simp]
theorem map
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [u.IsContinuous J K]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (homFunctor I I'.target))
    {F G : S ⟶ S'} (eta : F ⟶ G) :
    (mapHom.ofHomQuasiInverse I I' q).map eta =
      q.inverse.map (eta ▷ pullbackComparison I') := sorry

/-- Applying the inverse-image Hom functor after the explicit-choice construction recovers
postcomposition with the canonical pullback comparison, up to the supplied counit. -/
@[stacks 04WS "comparison for a Hom quasi-inverse presentation"]
noncomputable def comparisonIso
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [u.IsContinuous J K]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (homFunctor I I'.target)) :
    mapHom.ofHomQuasiInverse I I' q ⋙ homFunctor I I'.target ≅
      postcomp S (pullbackComparison I') :=
  Functor.QuasiInverse.liftFunctor.comparisonIso q
    (postcomp S (pullbackComparison I'))

/-- Different specified quasi-inverses produce naturally isomorphic inverse-image morphism
functors. The comparison is inherited from the generic uniqueness of quasi-inverse functors. -/
@[stacks 04WS "choice comparison for a Hom quasi-inverse presentation"]
noncomputable def choiceIso
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [u.IsContinuous J K]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q q' : Functor.QuasiInverse (homFunctor I I'.target)) :
    mapHom.ofHomQuasiInverse I I' q ≅ mapHom.ofHomQuasiInverse I I' q' :=
  Functor.QuasiInverse.liftFunctor.choiceIso q q'
    (postcomp S (pullbackComparison I'))

/-- The explicit-choice inverse-image functor is an equivalence under the hypotheses of
Lemma 8.12.12 (2). -/
@[stacks 04WS "equivalence of a Hom quasi-inverse presentation", instance]
instance isEquivalence
    [HasFiniteLimits C] [PreservesFiniteLimits u]
    [u.IsContinuous J K] [u.IsCocontinuous J K] [u.Full] [u.Faithful]
    {S S' : StackOver.{uC, vC,
      max w₀ (max uC (max uD (max vC vD))),
      max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (homFunctor I I'.target)) :
    Functor.IsEquivalence (mapHom.ofHomQuasiInverse I I' q) := sorry

end mapHom.ofHomQuasiInverse

-- Data audit: the quasi-inverse is supplied explicitly, and the resulting functor is the generic
-- `liftFunctor` applied to postcomposition with `pullbackComparison`.

end StackOver.InverseImage

end CategoryTheory
