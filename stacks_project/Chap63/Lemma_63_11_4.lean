module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.UpperShriek.Bounds
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open DerivedCategory
open DerivedCategory.TStructure

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
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).IsLeftAdjoint]

/- Lemma 63.11.4: Let $f : X \to Y$ be a finite type separated morphism of quasi-compact and quasi-separated schemes. Let $\Lambda$ be a torsion ring. The functor $Rf^!$ sends $D^+(Y_{\acute{e}tale}, \Lambda)$ into $D^+(X_{\acute{e}tale}, \Lambda)$. More precisely, there exists an integer $N \geq 0$ such that if $K \in D(Y_{\acute{e}tale}, \Lambda)$ has $H^i(K) = 0$ for $i < a$ then $H^i(Rf^!K) = 0$ for $i < a - N$. -/
@[stacks 0GLA] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriek.exists_mapsGE X Λ P :
    AddMonoid.IsTorsion Λ → ∃ N : ℕ, Functor.TStructure.MapsGE
      (etaleDerivedUpperShriek X Λ P) t t (-(N : ℤ)))

#check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriek.exists_isGE X Λ P :
    AddMonoid.IsTorsion Λ →
      ∃ N : ℕ, ∀ (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
        (a : ℤ), IsGE K a →
          IsGE ((etaleDerivedUpperShriek X Λ P).obj K) (a - N))

#check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedUpperShriek.isBoundedBelow X Λ P :
    AddMonoid.IsTorsion Λ →
      ∀ (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))),
        DerivedCategory.IsBoundedBelow K →
          DerivedCategory.IsBoundedBelow ((etaleDerivedUpperShriek X Λ P).obj K))

end AlgebraicGeometry.Scheme.Etale

end
