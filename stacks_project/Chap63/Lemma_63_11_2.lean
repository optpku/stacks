module

public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Lemma_63_11_2_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Agreement of derived upper shriek presentations for quasi-finite morphisms
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.QuasiFinite X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [IsFinite P.obj.right.hom]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [PreservesFiniteLimits
  ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology)]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Compactification.Of.ι P)).op]
variable [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]

/-- Lemma 63.11.2: Let `f = X.hom : X.left ⟶ Y` be a separated quasi-finite
morphism of quasi-compact quasi-separated schemes, and let `Λ` be a torsion
coefficient ring. Then the functor
`Rf^! = etaleDerivedUpperShriek X Λ P : D(Y_étale, Λ) ⥤ D(X_étale, Λ)` of
Lemma 63.11.1 is the same as the functor
`Rf^! = upperShriekModuleDerived X.hom Λ` of Lemma 63.7.1. The identification
is the uniqueness-of-adjoints isomorphism along `Rf_! ≅ f_!` from
Lemma 63.10.3, on a finite compactification `P`. -/
@[stacks 0GL8]
def etaleDerivedUpperShriekIso (hΛ : AddMonoid.IsTorsion Λ) :
    etaleDerivedUpperShriek X Λ P ≅ upperShriekModuleDerived X.hom Λ :=
  (fun _ ↦ etaleDerivedUpperShriekComparisonIso X Λ P) hΛ

/-- The identification `Rf^! K ≅ upperShriekModuleDerived K` at an object of
`D(Y_étale, Λ)`. -/
def etaleDerivedUpperShriekIso_app (hΛ : AddMonoid.IsTorsion Λ)
    (K : EtaleDerived Y Λ) :
    (etaleDerivedUpperShriek X Λ P).obj K ≅
      (upperShriekModuleDerived X.hom Λ).obj K :=
  (etaleDerivedUpperShriekIso X Λ P hΛ).app K

/-- The source-facing uniqueness isomorphism is the comparison mate of
`etaleDerivedLowerShriekIsoModuleDerived`. -/
theorem etaleDerivedUpperShriekIso_spec (hΛ : AddMonoid.IsTorsion Λ) :
    etaleDerivedUpperShriekIso X Λ P hΛ =
      etaleDerivedUpperShriekComparisonIso X Λ P :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
