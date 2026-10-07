module

public import stacks_project.Chap59.Lemma_59_102_5_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 59.102.5

Torsion coefficients in the ph/étale comparison of section 59.102 satisfy the vanishing and
derived identities of Situation 21.30.1.  Inverse image `a_X⁻¹` is the composite
`π_X⁻¹ ⋙ ε_X⁻¹` on the iterated slice owned by `PhComparison.situation`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PhComparison
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

/-- Lemma 59.102.5 (1): for `X` in `(Sch/S)_ph` and an abelian torsion sheaf `F` on
`X_étale`, the comparison unit identifies `ε_{X,*} (a_X⁻¹ F)` with `π_X⁻¹ F`. -/
@[stacks 0DE4]
theorem epsilon_pushforward_aInverseImage_unit_isIso {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    IsIso
      ((comparisonTopologyAdjunction AddCommGrpCat.{u + 1} (etale_le_ph S) X).unit.app
        ((piInverseImage X).obj F)) := sorry

/-- Lemma 59.102.5 (2): for `X` in `(Sch/S)_ph`, an abelian torsion sheaf `F` on
`X_étale`, and `0 < i`, the higher direct images `R^i ε_{X,*} (a_X⁻¹ F)` vanish. -/
@[stacks 0DE4]
theorem epsilon_rightDerived_aInverseImage_isZero {S : Scheme.{u}} {X : Over S}
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) (hi : 0 < i) :
    IsZero
      (((comparisonTopologyPushforwardAb (etale_le_ph S) X).rightDerived i).obj
        ((aInverseImage X).obj F)) := sorry

/-- Lemma 59.102.5 (3): for a proper morphism `f : X ⟶ Y` in `(Sch/S)_ph` and an abelian
torsion sheaf `F` on `X_étale`, inverse image along `a` identifies
`R^i f_small,* F` with `R^i f_big,ph,* (a_X⁻¹ F)`. -/
@[stacks 0DE4]
theorem proper_aInverseImage_higherDirectImage {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) (hf : properOver S f)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) :
    IsIsomorphic
      ((aInverseImage Y).obj (((smallPushforwardAb f.left).rightDerived i).obj F))
      ((Derived.Over.pushforwardDegree (Scheme.bigPhSite S) f i).obj
        ((aInverseImage X).obj F)) := sorry

/-- Lemma 59.102.5 (4): for a scheme `X` and `K` in `D⁺(X_étale)` with torsion
cohomology sheaves, the comparison unit `π_X⁻¹ K ⟶ Rε_{X,*} (a_X⁻¹ K)` is an
isomorphism. -/
@[stacks 0DE4]
theorem plus_piInverseImage_unit_isIso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso
      ((Derived.Plus.unit (etale_le_ph X) (Over.mk (𝟙 X))).app
        ((plusPiInverseImage (Over.mk (𝟙 X))).obj K)) := sorry

/-- Lemma 59.102.5 (5): for a proper morphism `f : X ⟶ Y` of schemes and `K` in
`D⁺(X_étale)` with torsion cohomology sheaves, the canonical mate
`a_Y⁻¹ (Rf_small,* K) ⟶ Rf_big,ph,* (a_X⁻¹ K)` is an isomorphism. -/
@[stacks 0DE4]
theorem proper_plusSmallPhPushforward_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso ((plusSmallPhPushforwardHom f).app K) := sorry

end AlgebraicGeometry.Scheme.PhComparison

end

end
