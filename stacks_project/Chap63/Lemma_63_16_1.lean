module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.UpperShriek.AffineCohomology
import StacksCheckRecall

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
    (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))).IsLeftAdjoint]
variable [∀ U : Scheme.{u}, HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (U V : Scheme.{u}) (f : U ⟶ V) [Etale f]
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (etaleRestriction f).op.HasLeftKanExtension F]
variable [HasSheafify (AffineEtale.topology X.left) (ModuleCat.{u} Λ)]
variable [((etaleDerivedLowerShriek X P :
    (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))).CommShift ℤ]

/- Lemma 63.16.1: the affine restriction of the cohomology sheaf of derived
upper shriek is the sheafification of the trace-induced Hom presheaf. -/
@[stacks 0GLK] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriek_cohomology_affineEtale
    Λ X P : ∀ (hΛ : AddMonoid.IsTorsion Λ) (K : (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) (n : ℤ),
      let _ := hΛ
      IsIso (etaleDerivedUpperShriekCohomologyAffineComparison Λ X P K n))

end
