module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport.Coproduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
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

section CoproductComparison

variable {I : Type u} (K : I → DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
variable [HasCoproductsOfShape I (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))]
variable [HasCoproductsOfShape I (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))]

#check (CategoryTheory.Limits.sigmaComparison (etaleDerivedLowerShriek X P) K :
  (∐ fun i ↦ (etaleDerivedLowerShriek X P).obj (K i)) ⟶
    (etaleDerivedLowerShriek X P).obj (∐ K))

#check (CategoryTheory.Limits.ι_comp_sigmaComparison
  (etaleDerivedLowerShriek X P) K :
  ∀ i : I,
    Sigma.ι (fun j ↦ (etaleDerivedLowerShriek X P).obj (K j)) i ≫
        CategoryTheory.Limits.sigmaComparison (etaleDerivedLowerShriek X P) K =
      (etaleDerivedLowerShriek X P).map (Sigma.ι K i))

variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/- Lemma 63.10.1 (1): derived lower shriek commutes with direct sums of
uniformly bounded-below families with torsion cohomology sheaves. -/
@[stacks 0G29] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek_preservesCoproduct X P K :
    ∀ (a : ℤ), (∀ i, DerivedCategory.IsGE (K i) a) →
      (∀ i, etaleDerivedIsTorsion (K i)) →
      IsIso (CategoryTheory.Limits.sigmaComparison (etaleDerivedLowerShriek X P) K))

end CoproductComparison

variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]

/- Lemma 63.10.1 (2): derived lower shriek preserves arbitrary direct sums
when the coefficient ring is additively torsion. -/
@[stacks 0G29] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek_preservesCoproducts X P :
    ∀ (hΛ : AddMonoid.IsTorsion Λ) (I : Type u),
      [HasCoproductsOfShape I (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))] →
      [HasCoproductsOfShape I (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))] →
      PreservesColimitsOfShape (Discrete I)
        (etaleDerivedLowerShriek X P :
          DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))

end AlgebraicGeometry.Scheme.Etale

end
