/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport.Constructible
import StacksCheckRecall

/-!
# Constructible cohomology of compact-support pushforward of a constant sheaf

If `S` is Noetherian affine of finite dimension and `X.hom : X.left ⟶ S` is
separated, affine, and smooth of relative dimension `1`, then `Rf_!` of a
constant sheaf of a finite module over a Noetherian torsion ring has
constructible cohomology.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} (X : Over S)
variable [IsAffine S] [IsNoetherian S]
variable [IsSeparated X.hom] [IsAffineHom X.hom]
variable [SmoothOfRelativeDimension 1 X.hom] [Scheme.Hom.FiniteType X.hom]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable {M : Type u} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
variable (P : Compactification.Of S X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : S.Etale,
  HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) S.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) S.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ S) (G : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]

/- Lemma 63.14.2: if `S` is a Noetherian affine scheme of finite dimension,
`X.hom` is separated, affine, and smooth of relative dimension `1`, and `M`
is a finite module over a Noetherian torsion ring, then the compact-support
pushforward of the constant étale sheaf of `M` has constructible cohomology. -/
@[stacks 0GKX] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek_constantModule_cohomology_isConstructible X (M := M) P :
  AddMonoid.IsTorsion Λ → topologicalKrullDim S < ⊤ →
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            S.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek X P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
          ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (.of Λ M)))))

/- Every integer-degree homology sheaf is constructible. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.constantModule_homology_isConstructible X (M := M) P :
  AddMonoid.IsTorsion Λ → topologicalKrullDim S < ⊤ → ∀ n : ℤ,
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          S.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
        ((etaleDerivedLowerShriek X P).obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (0 : ℤ)).obj
            ((constantSheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
              (.of Λ M))))))

end AlgebraicGeometry.Scheme.Etale

end
