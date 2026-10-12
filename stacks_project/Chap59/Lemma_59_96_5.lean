/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ModuleTensor
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

universe u v

/- Lemma 59.96.5 - derived global sections commute with tensoring by a constant complex. -/
@[stacks 0F12] #check
  (AlgebraicGeometry.Scheme.Etale.rGamma_tensor_constant_module :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type v} [CommRing Λ]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
    [((X.smallEtaleTopology.W :
      MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ))).IsMonoidal]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (ModuleCat.{v} Λ)]
    [MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [∀ (K L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) (ComplexShape.up ℤ)]
    [∀ (K L : CochainComplex (ModuleCat.{v} Λ) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (ModuleCat.{v} Λ)) (ComplexShape.up ℤ)]
    [DerivedTensor.Right.Has (C := Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [DerivedTensor.Right.Has (C := ModuleCat.{v} Λ)]
    [(constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ)).Additive]
    [PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [PreservesFiniteColimits (constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [((sheafSections X.smallEtaleTopology (ModuleCat.{v} Λ)).obj
      (op (globalEtale X))).Additive]
    [Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections X.smallEtaleTopology (ModuleCat.{v} Λ)).obj
          (op (globalEtale X))))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) (ComplexShape.up ℤ))]
    (hcd : cohomologicalDimension X ≠ ⊤)
    (hΛ : AddMonoid.IsTorsion Λ)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (K : DerivedCategory (ModuleCat.{v} Λ)),
    Nonempty
      ((RightDerived.Cochain.functor
            ((sheafSections X.smallEtaleTopology (ModuleCat.{v} Λ)).obj
              (op (globalEtale X)))).obj
          (E ⊗ᴸ
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{v} Λ)).mapDerivedCategory.obj K)) ≅
        ((RightDerived.Cochain.functor
            ((sheafSections X.smallEtaleTopology (ModuleCat.{v} Λ)).obj
              (op (globalEtale X)))).obj E) ⊗ᴸ
          K))
