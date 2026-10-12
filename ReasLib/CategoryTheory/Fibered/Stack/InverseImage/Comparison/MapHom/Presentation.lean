/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.HomComparison
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison.MapHom.OfHomQuasiInverse.Universal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentation independence for inverse-image morphism functors

This file compares the direct stackification construction with the construction obtained from a
quasi-inverse of the canonical Hom functor.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Bicategory Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage.mapHom

variable {u : C ⥤ D}
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable [u.IsContinuous J K]

variable {S S' : StackOver.{uC, vC,
  max w₀ (max uC (max uD (max vC vD))),
  max w₁ (max w₀ (max uC (max uD (max vC vD))))} J}

/-- The direct stackification presentation of inverse-image morphisms is naturally isomorphic
to the presentation obtained from any explicit quasi-inverse of the canonical Hom functor. -/
@[stacks 04WS "presentation independence for inverse-image morphisms"]
noncomputable def homQuasiInverseIso
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target)) :
    mapHom I I' h q_stack ≅ mapHom.ofHomQuasiInverse I I' q_hom :=
  mapHom.ofHomQuasiInverse.isoOfComparison I I' q_hom
    (mapHom I I' h q_stack) (homFunctorIso I I' h q_stack)

/-- The forward component of presentation independence first uses the adjointified Hom
quasi-inverse unit and then applies that inverse to the direct Hom comparison. -/
@[simp, stacks 04WS "inverse-image presentation forward component"]
theorem homQuasiInverseIso.hom.app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (homQuasiInverseIso I I' h q_stack q_hom).hom.app F =
      q_hom.adjointifyUnit.unitIso.hom.app ((mapHom I I' h q_stack).obj F) ≫
        q_hom.inverse.map ((homFunctorIso I I' h q_stack).hom.app F) := sorry

/-- The inverse component of presentation independence applies the Hom quasi-inverse to the
inverse direct comparison and then uses the adjointified Hom quasi-inverse unit backwards. -/
@[simp, stacks 04WS "inverse-image presentation inverse component"]
theorem homQuasiInverseIso.inv.app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (homQuasiInverseIso I I' h q_stack q_hom).inv.app F =
      q_hom.inverse.map ((homFunctorIso I I' h q_stack).inv.app F) ≫
        q_hom.adjointifyUnit.unitIso.inv.app
          ((mapHom I I' h q_stack).obj F) := sorry

set_option maxHeartbeats 800000 in
/-- Presentation independence intertwines the direct Hom comparison with the canonical
comparison of the Hom-quasi-inverse presentation. -/
@[stacks 04WS "inverse-image presentation comparison coherence"]
theorem homQuasiInverseIso.comparison
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target)) :
    Functor.isoWhiskerRight
          (homQuasiInverseIso I I' h q_stack q_hom)
          (homFunctor I I'.target) ≪≫
        mapHom.ofHomQuasiInverse.comparisonIso I I' q_hom =
      homFunctorIso I I' h q_stack := sorry

/-- Compatibility with the direct Hom comparison uniquely characterizes presentation
independence. This form lets later coherence proofs avoid componentwise diagram chases. -/
@[stacks 04WS "inverse-image presentation uniqueness characterization"]
theorem homQuasiInverseIso.eq_iff
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target))
    (beta : mapHom I I' h q_stack ≅
      mapHom.ofHomQuasiInverse I I' q_hom) :
    beta = homQuasiInverseIso I I' h q_stack q_hom ↔
      Functor.isoWhiskerRight beta (homFunctor I I'.target) ≪≫
          mapHom.ofHomQuasiInverse.comparisonIso I I' q_hom =
        homFunctorIso I I' h q_stack := sorry

set_option maxHeartbeats 800000 in
/-- The forward presentation-independence triangle commutes on every stack morphism. -/
@[stacks 04WS "inverse-image presentation forward naturality"]
theorem homQuasiInverseIso.hom.comparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (homFunctor I I'.target).map
          ((homQuasiInverseIso I I' h q_stack q_hom).hom.app F) ≫
        (mapHom.ofHomQuasiInverse.comparisonIso I I' q_hom).hom.app F =
      (homFunctorIso I I' h q_stack).hom.app F := sorry

set_option maxHeartbeats 800000 in
/-- The inverse presentation-independence triangle commutes on every stack morphism. -/
@[stacks 04WS "inverse-image presentation inverse naturality"]
theorem homQuasiInverseIso.inv.comparison_app
    (I : StackOver.InverseImage K u S)
    (I' : StackOver.InverseImage K u S')
    (h : FiberedCategoryOver.Pushforward.InversionChoice u
      S.toFiberedCategoryOver S'.toFiberedCategoryOver)
    (q_stack : Functor.QuasiInverse
      (StackOver.Hom.precomp I'.target I.comparisonHom))
    (q_hom : Functor.QuasiInverse (homFunctor I I'.target))
    (F : S ⟶ S') :
    (mapHom.ofHomQuasiInverse.comparisonIso I I' q_hom).inv.app F ≫
        (homFunctor I I'.target).map
          ((homQuasiInverseIso I I' h q_stack q_hom).inv.app F) =
      (homFunctorIso I I' h q_stack).inv.app F := sorry

/- Axiom audit: `homQuasiInverseIso` uses the data-clean generic quasi-inverse lift comparison;
`sorryAx` is confined to theorem-valued coherence and inherited proof fields. -/

end StackOver.InverseImage.mapHom

end CategoryTheory
