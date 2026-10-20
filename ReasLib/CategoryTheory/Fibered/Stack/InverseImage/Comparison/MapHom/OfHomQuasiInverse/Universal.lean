module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.OfHomQuasiInverse

/-!
# Universal property of the Hom-quasi-inverse presentation

This leaf specializes quasi-inverse lift uniqueness to inverse-image morphism functors. It keeps
the public comparison surface in the language of `homFunctor` and `pullbackComparison`.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {u : C ⥤ D}
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable [u.IsContinuous J K]

namespace StackOver.InverseImage.mapHom.ofHomQuasiInverse

variable {S S' : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}

/-- A candidate inverse-image Hom lift with the canonical comparison is uniquely isomorphic to
the lift formed from the explicit Hom quasi-inverse. -/
@[stacks 04WS "Hom-quasi-inverse comparison presentation"]
noncomputable def isoOfComparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (homFunctor I I'.target))
    (L : (S ⟶ S') ⥤ (I.target ⟶ I'.target))
    (alpha : L ⋙ homFunctor I I'.target ≅
      postcomp S (pullbackComparison I')) :
    L ≅ mapHom.ofHomQuasiInverse I I' q :=
  Functor.QuasiInverse.liftFunctor.isoOfComparison q L
    (postcomp S (pullbackComparison I')) alpha

/-- The universal inverse-image Hom-lift isomorphism recovers its supplied comparison. -/
@[stacks 04WS "Hom-quasi-inverse comparison presentation coherence"]
theorem isoOfComparison.comparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (homFunctor I I'.target))
    (L : (S ⟶ S') ⥤ (I.target ⟶ I'.target))
    (alpha : L ⋙ homFunctor I I'.target ≅
      postcomp S (pullbackComparison I')) :
    Functor.isoWhiskerRight (isoOfComparison I I' q L alpha)
          (homFunctor I I'.target) ≪≫
        comparisonIso I I' q =
      alpha := sorry

/-- Compatibility with the Hom comparison uniquely characterizes the universal inverse-image
Hom-lift isomorphism. -/
@[stacks 04WS "Hom-quasi-inverse comparison presentation uniqueness"]
theorem isoOfComparison.eq_iff
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (homFunctor I I'.target))
    (L : (S ⟶ S') ⥤ (I.target ⟶ I'.target))
    (alpha : L ⋙ homFunctor I I'.target ≅
      postcomp S (pullbackComparison I'))
    (beta : L ≅ mapHom.ofHomQuasiInverse I I' q) :
    beta = isoOfComparison I I' q L alpha ↔
      Functor.isoWhiskerRight beta (homFunctor I I'.target) ≪≫
          comparisonIso I I' q =
        alpha := sorry

/-- Applying Hom-lift uniqueness to the canonical comparison gives the identity isomorphism. -/
@[simp, stacks 04WS "Hom-quasi-inverse comparison presentation self"]
theorem isoOfComparison.self
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (q : Functor.QuasiInverse (homFunctor I I'.target)) :
    isoOfComparison I I' q (mapHom.ofHomQuasiInverse I I' q)
        (comparisonIso I I' q) =
      Iso.refl (mapHom.ofHomQuasiInverse I I' q) := sorry

/- Axiom audit: the isomorphism is the generic data-clean universal comparison specialized to
the explicit inverse-image Hom functor; proof debt remains in theorem-valued coherence only. -/

end StackOver.InverseImage.mapHom.ofHomQuasiInverse

end CategoryTheory
