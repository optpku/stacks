module

public import stacks_project.Chap63.Lemma_63_10_3_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Agreement of derived and exact lower shriek for quasi-finite morphisms
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

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
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

/-- Lemma 63.10.3: Let `f = X.hom : X.left ⟶ Y` be a quasi-finite separated
morphism of quasi-compact quasi-separated schemes. Then the functors
`Rf_! = etaleDerivedLowerShriek X P` constructed in Section 63.9 agree with
the exact functor `f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Section 63.7, on
their common domains. On a finite compactification `P` this exact functor is
`π_* ∘ j_!` (`etaleDerivedExactLowerShriek`), using Zariski's Main Theorem,
`Rπ_* = π_*` for finite `π`, and `π_* ∘ j_! = f_!`. -/
@[stacks 0GKM]
def etaleDerivedLowerShriekIso :
    (etaleDerivedLowerShriek X P :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ≅
      etaleDerivedExactLowerShriek X P :=
  etaleDerivedLowerShriekComparisonIso X P

/-- The forward map of `etaleDerivedLowerShriekIso` is the compactification
comparison natural transformation. -/
theorem etaleDerivedLowerShriekIso_hom :
    (etaleDerivedLowerShriekIso X P).hom =
      (etaleDerivedLowerShriekComparison X P :
        (etaleDerivedLowerShriek X P :
            EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⟶
          etaleDerivedExactLowerShriek X P) :=
  sorry

/-- The identification `Rf_! K ≅ (π_* ∘ j_!) K` at an object of
`D(X_étale, Λ)`. -/
theorem etaleDerivedLowerShriekIso_app (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriekIso X P).app K =
      (etaleDerivedLowerShriekComparisonIso X P).app K :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
