module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek

/-!
# Derived upper shriek for étale torsion coefficients

The functor `Rf^!` is the chosen right adjoint of the compactification
presentation `Rf_! = etaleDerivedLowerShriek`. Existence of the adjoint is
an ambient Brown-representability hypothesis; this file does not instantiate
it.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Compactification.Of Y X)
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
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]

/-- The derived upper shriek `Rf^!`, the chosen right adjoint of
`etaleDerivedLowerShriek`. -/
def etaleDerivedUpperShriek : EtaleDerived Y Λ ⥤ EtaleDerived X.left Λ :=
  (etaleDerivedLowerShriek X P).rightAdjoint

/-- Derived upper shriek is the chosen right adjoint of `Rf_!`. -/
theorem etaleDerivedUpperShriek_def :
    etaleDerivedUpperShriek X Λ P = (etaleDerivedLowerShriek X P).rightAdjoint :=
  sorry

/-- The adjunction `Rf_! ⊣ Rf^!` on unbounded derived categories of étale
`Λ`-modules. -/
def etaleDerivedLowerShriekAdjunction :
    etaleDerivedLowerShriek X P ⊣ etaleDerivedUpperShriek X Λ P :=
  Adjunction.ofIsLeftAdjoint (etaleDerivedLowerShriek X P)

/-- The hom-equivalence of the derived compact-support adjunction. -/
def etaleDerivedLowerShriekAdjunction_homEquiv
    (L : EtaleDerived X.left Λ) (K : EtaleDerived Y Λ) :
    ((etaleDerivedLowerShriek X P).obj L ⟶ K) ≃
      (L ⟶ (etaleDerivedUpperShriek X Λ P).obj K) :=
  (etaleDerivedLowerShriekAdjunction X Λ P).homEquiv L K

end AlgebraicGeometry.Scheme.Etale

end
