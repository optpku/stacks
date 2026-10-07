module

public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Lemma_63_16_1_HomPresheaf
public import stacks_project.Chap63.Lemma_63_16_1_UpperShriek
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
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
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]
variable [Linear Λ (EtaleDerived Y Λ)]
variable [Linear Λ (EtaleDerived X.left Λ)]
variable [∀ U : Scheme.{u}, HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (U V : Scheme.{u}) (f : U ⟶ V) [Etale f]
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (etaleRestriction f).op.HasLeftKanExtension F]
variable [HasSheafify (AffineEtale.topology X.left) (ModuleCat.{u} Λ)]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).CommShift ℤ]

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 63.16.1: for a separated finite-type morphism `X.hom : X.left ⟶ Y`
of quasi-compact quasi-separated schemes, a torsion ring `Λ`, and
`K` in `D(Y_étale, Λ)`, the cohomology sheaf `H^n(Rf^! K)` restricted to
`X_affine,étale` is the sheaf associated to the presheaf
`U ↦ Hom_Y(R(U ⟶ Y)_! Λ, K⟦n⟧)`, using the covariant functoriality of
`R(U ⟶ Y)_! Λ` along étale maps. -/
@[stacks 0GLK]
theorem etaleDerivedUpperShriek_cohomology_affineEtale
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived Y Λ) (n : ℤ) :
    IsIso (etaleDerivedUpperShriekCohomologyAffineComparison Λ X P K n) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
