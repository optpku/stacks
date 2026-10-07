module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import stacks_project.Chap59.Lemma_59_100_6_InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fppf/étale derived comparisons

This leaf owns the six source-facing comparison theorems of Lemma 59.100.6: the underived
`ε_* a⁻¹` identification and vanishing, the finite higher-direct-image comparison, the
bounded-below derived unit, and the finite / proper-with-torsion derived pushforward
identifications.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FppfEtale

/-- Lemma 59.100.6 (1): for an abelian sheaf `F` on `X_étale`, the canonical map
`π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)` is an isomorphism. -/
@[stacks 0DDS]
theorem aInverse_unit_isIso {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (aInverse_unit X F) := sorry

/-- Lemma 59.100.6 (2): for an abelian sheaf `F` on `X_étale` and `0 < i`, the higher
direct images `R^i ε_{X,*}(a_X⁻¹ F)` vanish. -/
@[stacks 0DDS]
theorem aInverse_higherDirectImage_isZero {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) (hi : 0 < i) :
    IsZero
      (((epsilonPushforward X).rightDerived i).obj ((aInverseAb X).obj F)) := sorry

/-- Lemma 59.100.6 (3): for a finite morphism `f : X ⟶ Y` and an abelian sheaf `F` on
`X_étale`, inverse image along `a` identifies `R^i f_small,* F` with
`R^i f_big,fppf,* (a_X⁻¹ F)`. -/
@[stacks 0DDS]
theorem finite_higherDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (i : ℕ) :
    IsIsomorphic
      ((aInverseAb Y).obj (((smallPushforwardAb f).rightDerived i).obj F))
      (((fppfPushforwardAb f).rightDerived i).obj ((aInverseAb X).obj F)) := sorry

/-- Lemma 59.100.6 (4): for `K` in `D⁺(X_étale)`, the canonical map
`π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)` is an isomorphism. -/
@[stacks 0DDS]
theorem derivedUnit_isIso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIso ((Derived.Plus.unit etale_le_fppf X).app ((piInverseImagePlus X).obj K)) :=
  sorry

/-- Lemma 59.100.6 (5): for a finite morphism `f : X ⟶ Y` and `K` in `D⁺(X_étale)`,
inverse image along `a` identifies `Rf_small,* K` with `Rf_big,fppf,* (a_X⁻¹ K)`. -/
@[stacks 0DDS]
theorem finite_derivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((aInverseAbPlus Y).obj
        ((Adjunction.Derived.Plus.right (smallPushforwardAb f)).obj K))
      ((Derived.Over.Plus.pushforward fppfTopology f).obj
        ((aInverseAbPlus X).obj K)) := sorry

/-- Lemma 59.100.6 (6): for a proper morphism `f : X ⟶ Y` and `K` in `D⁺(X_étale)`
with locally torsion cohomology sheaves, inverse image along `a` identifies
`Rf_small,* K` with `Rf_big,fppf,* (a_X⁻¹ K)`. -/
@[stacks 0DDS]
theorem proper_torsion_derivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIsomorphic
      ((aInverseAbPlus Y).obj
        ((Adjunction.Derived.Plus.right (smallPushforwardAb f)).obj K))
      ((Derived.Over.Plus.pushforward fppfTopology f).obj
        ((aInverseAbPlus X).obj K)) := sorry

end AlgebraicGeometry.Scheme.FppfEtale

end
