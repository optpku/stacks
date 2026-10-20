/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ZMod
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bifunctor.FixedRight
public import Mathlib.FieldTheory.IsSepClosed

public import ReasLib.CategoryTheory.Sites.AbelianTensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Universe
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.BoundedBelow
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute

/-! # The Künneth formula for étale cohomology -/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf CategoryTheory.DerivedCategory Opposite
open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.Hom
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section

variable {k : Type u} [Field k] [IsSepClosed k]
variable (X Y : SchemeOverField k)
variable [Algebraic X] [Algebraic Y]
variable [HasPullback X.hom Y.hom]
variable (n : ℕ) [NeZero n]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory (ModuleCat.{u} (ZMod n))]
variable [∀ (K L : CochainComplex (ModuleCat.{u} (ZMod n)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (ModuleCat.TensorProduct.functor (ZMod n)) (ComplexShape.up ℤ)]
variable [∀ E : DerivedCategory (ModuleCat.{u} (ZMod n)),
    Functor.HasLeftDerivedFunctor
      (Bifunctor.Right.sourceFunctor (ModuleCat.TensorProduct.functor (ZMod n)) E)
      (HomotopyCategory.quasiIso (ModuleCat.{u} (ZMod n)) (ComplexShape.up ℤ))]
variable [∀ (K L : CochainComplex
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (ModuleCat.TensorProduct.Sheaf.functor
        (pullback X.hom Y.hom).smallEtaleTopology (ZMod n)) (ComplexShape.up ℤ)]
variable [∀ E : DerivedCategory
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))),
    Functor.HasLeftDerivedFunctor
      (Bifunctor.Right.sourceFunctor
        (ModuleCat.TensorProduct.Sheaf.functor
          (pullback X.hom Y.hom).smallEtaleTopology (ZMod n)) E)
      (HomotopyCategory.quasiIso
        (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n)))
        (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u},
    ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
      (op (globalEtale Z))).Additive]
variable [∀ Z : Scheme.{u},
    Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
          (op (globalEtale Z))))
      (HomologicalComplex.quasiIso
        (Sheaf Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ))]

/-- Over a separably closed field, derived global sections of the external derived tensor
product of arbitrary étale `ZMod n` complexes on finite-type schemes identify with the derived
tensor product of their derived global sections, when `n` is positive and invertible. -/
theorem rGamma_kunneth_zmod_of_finiteType
    (h_n : IsUnit (n : k))
    (E : DerivedCategory
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (K : DerivedCategory
      (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    Nonempty
      ((RightDerived.Cochain.functor
            ((sheafSections (pullback X.hom Y.hom).smallEtaleTopology
                (ModuleCat.{u} (ZMod n))).obj
              (op (globalEtale (pullback X.hom Y.hom))))).obj
          (Bifunctor.Right.obj
            (ModuleCat.TensorProduct.Sheaf.functor
              (pullback X.hom Y.hom).smallEtaleTopology (ZMod n))
            ((zmodDerivedInverseImage (pullback.fst X.hom Y.hom) n).obj E)
            ((zmodDerivedInverseImage (pullback.snd X.hom Y.hom) n).obj K)) ≅
        Bifunctor.Right.obj (ModuleCat.TensorProduct.functor (ZMod n))
          ((RightDerived.Cochain.functor
              ((sheafSections X.left.smallEtaleTopology
                  (ModuleCat.{u} (ZMod n))).obj
                (op (globalEtale X.left)))).obj E)
          ((RightDerived.Cochain.functor
              ((sheafSections Y.left.smallEtaleTopology
                  (ModuleCat.{u} (ZMod n))).obj
                (op (globalEtale Y.left)))).obj K)) := sorry

end

variable {k : Type u} [Field k]
variable (X Y : SchemeOverField k)
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [HasPullback X.hom Y.hom]

section

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [((pullback X.hom Y.hom).smallEtaleTopology.W
    (A := AddCommGrpCat.{u})).IsMonoidal]
variable [MonoidalPreadditive AddCommGrpCat.{u}]
variable [∀ (K L : CochainComplex AddCommGrpCat.{u} ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor AddCommGrpCat.{u}) (ComplexShape.up ℤ)]
variable [hAbTensor : DerivedTensor.Right.Has (C := AddCommGrpCat.{u})]
variable [MonoidalPreadditive
    (Sheaf (pullback X.hom Y.hom).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ (K L : CochainComplex
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology AddCommGrpCat.{u}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (Sheaf (pullback X.hom Y.hom).smallEtaleTopology AddCommGrpCat.{u}))
      (ComplexShape.up ℤ)]
variable [hXYTensor :
    DerivedTensor.Right.Has
      (C := Sheaf (pullback X.hom Y.hom).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    ((sheafSections Z.smallEtaleTopology AddCommGrpCat.{u}).obj
      (op (globalEtale Z))).Additive]
variable [∀ Z : Scheme.{u},
    Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Z.smallEtaleTopology AddCommGrpCat.{u}).obj
          (op (globalEtale Z))))
      (HomologicalComplex.quasiIso
        (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/-- If `k` is a separably closed field, `X` is proper over `k`,
`Y` is quasi-compact and quasi-separated over `k`, `E ∈ D⁺(X_étale)` has torsion
cohomology sheaves, and `K ∈ D⁺(Y_étale)`, then
`RΓ(X ×_{Spec k} Y, pr₁⁻¹ E ⊗ᴸ pr₂⁻¹ K)` is isomorphic in `D(Ab)` to
`RΓ(X, E) ⊗ᴸ RΓ(Y, K)`. -/
@[stacks 0F14]
theorem rGamma_kunneth
    [IsSepClosed k] [IsProper X.hom]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
    (E : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})) E)
    (K : DerivedCategory.Plus (Sheaf Y.left.smallEtaleTopology AddCommGrpCat.{u})) :
    Nonempty
      ((RightDerived.Cochain.functor
            ((sheafSections (pullback X.hom Y.hom).smallEtaleTopology
                AddCommGrpCat.{u}).obj
              (op (globalEtale (pullback X.hom Y.hom))))).obj
          (DerivedCategory.Plus.ι.obj
              ((etaleDerivedInverseImage (pullback.fst X.hom Y.hom)).obj E) ⊗ᴸ
            DerivedCategory.Plus.ι.obj
              ((etaleDerivedInverseImage (pullback.snd X.hom Y.hom)).obj K)) ≅
        ((RightDerived.Cochain.functor
              ((sheafSections X.left.smallEtaleTopology AddCommGrpCat.{u}).obj
                (op (globalEtale X.left)))).obj
            (DerivedCategory.Plus.ι.obj E) ⊗ᴸ
          (RightDerived.Cochain.functor
              ((sheafSections Y.left.smallEtaleTopology AddCommGrpCat.{u}).obj
                (op (globalEtale Y.left)))).obj
            (DerivedCategory.Plus.ι.obj K))) := sorry

end

section

variable (n : ℕ)
variable [∀ Z : Scheme.{u},
    HasSheafify Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory (ModuleCat.{u} (ZMod n))]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    PreservesFiniteLimits (zmodSheafPullback h n)]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B), (zmodSheafPullback h n).Additive]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B), (zmodSheafPushforward h n).Additive]
variable [((pullback X.hom Y.hom).smallEtaleTopology.W
    (A := ModuleCat.{u} (ZMod n))).IsMonoidal]
variable [MonoidalPreadditive (ModuleCat.{u} (ZMod n))]
variable [∀ (K L : CochainComplex (ModuleCat.{u} (ZMod n)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ)]
variable [hModTensor :
    DerivedTensor.Right.Has (C := ModuleCat.{u} (ZMod n))]
variable [MonoidalPreadditive
    (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ (K L : CochainComplex
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))))
      (ComplexShape.up ℤ)]
variable [hXYModTensor :
    DerivedTensor.Right.Has
      (C := Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ Z : Scheme.{u},
    ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
      (op (globalEtale Z))).Additive]
variable [∀ Z : Scheme.{u},
    Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))).obj
          (op (globalEtale Z))))
      (HomologicalComplex.quasiIso
        (Sheaf Z.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ))]

/-- Over a separably closed field, let `X` be proper and `Y` be of finite type.
For a nonzero modulus `n` and `E ∈ D(X_étale, ZMod n)` and `K ∈ D(Y_étale, ZMod n)` one has
`RΓ(X ×_{Spec k} Y, pr₁⁻¹ E ⊗ᴸ pr₂⁻¹ K) ≅ RΓ(X, E) ⊗ᴸ RΓ(Y, K)`
in `D(ModuleCat (ZMod n))`. -/
@[stacks 0F14]
theorem rGamma_kunneth_zmod
    [IsSepClosed k] [IsProper X.hom]
    [CompactSpace Y.left] [QuasiSeparatedSpace Y.left] [Algebraic Y] [NeZero n]
    (E : DerivedCategory
      (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod n))))
    (K : DerivedCategory
      (Sheaf Y.left.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    Nonempty
      ((RightDerived.Cochain.functor
            ((sheafSections (pullback X.hom Y.hom).smallEtaleTopology
                (ModuleCat.{u} (ZMod n))).obj
              (op (globalEtale (pullback X.hom Y.hom))))).obj
          ((zmodDerivedInverseImage (pullback.fst X.hom Y.hom) n).obj E ⊗ᴸ
            (zmodDerivedInverseImage (pullback.snd X.hom Y.hom) n).obj K) ≅
        ((RightDerived.Cochain.functor
              ((sheafSections X.left.smallEtaleTopology
                  (ModuleCat.{u} (ZMod n))).obj
                (op (globalEtale X.left)))).obj E ⊗ᴸ
          (RightDerived.Cochain.functor
              ((sheafSections Y.left.smallEtaleTopology
                  (ModuleCat.{u} (ZMod n))).obj
                (op (globalEtale Y.left)))).obj K)) := sorry

end

end AlgebraicGeometry.Scheme.Etale

end
