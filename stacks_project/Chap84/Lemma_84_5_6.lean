module

public import stacks_project.Chap84.Lemma_84_5_6_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.5.6

For a proper morphism of algebraic spaces, small and big étale direct images
agree after inverse image along `π`, on sheaves of sets, on `D⁺` with torsion
cohomology, and on all of `D` when the morphism is finite.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale
namespace SmallToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `plusSmallBigPushforwardHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

section Sets

/-- Lemma 84.5.6 (1): for a proper morphism `f : Y ⟶ X` of algebraic spaces over a
scheme `S`, the functors `π_X⁻¹ ∘ f_small,*` and `f_big,* ∘ π_Y⁻¹` from sheaves of
sets on `Y_étale` to sheaves of sets on `(Spaces/X)_étale` are canonically
isomorphic via `smallBigPushforwardHom`. -/
@[stacks 0DGD]
theorem proper_smallBigPushforward_isIso [Proper f] :
    IsIso (smallBigPushforwardHom f) := sorry

end Sets

section Plus

variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
variable [∀ P : (smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (relocalizationFunctor (𝟙 Y)).op.HasLeftKanExtension P]
variable [∀ P : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (Over.map f).op.HasPointwiseRightKanExtension P]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [PreservesFiniteLimits
    ((relocalizationFunctor (𝟙 X)).op.lan :
      ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
variable [PreservesFiniteLimits
    ((relocalizationFunctor (𝟙 Y)).op.lan :
      ((smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        ((Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian f).Additive]
variable [(bigAbelianPushforward f).Additive]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}))]
variable [(bigAbelianPushforward f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1}))]

/-- Lemma 84.5.6 (2): for a proper morphism `f : Y ⟶ X` and `K` in `D⁺(Y_étale)` whose
cohomology sheaves are locally torsion, the canonical mate
`π_X⁻¹ Rf_small,* K ⟶ Rf_big,* π_Y⁻¹ K` is an isomorphism. -/
@[stacks 0DGD]
theorem proper_smallBigDerivedPushforward_plus_isIso [Proper f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})) K) :
    IsIso ((plusSmallBigPushforwardHom f).app K) := sorry

end Plus

section Unbounded

variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (overEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
variable [∀ P : (smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (relocalizationFunctor (𝟙 Y)).op.HasLeftKanExtension P]
variable [∀ P : (Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (Over.map f).op.HasPointwiseRightKanExtension P]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [PreservesFiniteLimits
    ((relocalizationFunctor (𝟙 X)).op.lan :
      ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
variable [PreservesFiniteLimits
    ((relocalizationFunctor (𝟙 Y)).op.lan :
      ((smallEtaleSite Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
        ((Over Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian f).Additive]
variable [(bigAbelianPushforward f).Additive]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [IsGrothendieckAbelian (Sheaf (overEtaleTopology Y) AddCommGrpCat.{u + 1})]

/-- Lemma 84.5.6 (3): if `f : Y ⟶ X` is finite, then for every `K` in `D(Y_étale)` the
canonical mate `π_X⁻¹ Rf_small,* K ⟶ Rf_big,* π_Y⁻¹ K` is an isomorphism. -/
@[stacks 0DGD]
theorem finite_smallBigDerivedPushforward_isIso [IsFinite f]
    (K : DerivedCategory (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})) :
    IsIso ((unboundedSmallBigPushforwardHom f).app K) := sorry

end Unbounded

end SmallToBig
end AlgebraicGeometry.AlgebraicSpace.Etale

end

end
