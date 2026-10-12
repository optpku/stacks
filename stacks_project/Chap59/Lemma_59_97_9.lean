/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_92_3_BaseChange
public import stacks_project.Chap59.Theorem_59_51_3_Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf
open CategoryTheory.DerivedCategory
open Opposite
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k] [IsSepClosed k]
variable (X Y : SchemeOverField k)
variable [Algebraic X] [Algebraic Y]
variable [HasPullback X.hom Y.hom]
variable (n : ℕ) [NeZero n]
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
variable [MonoidalCategory (ModuleCat.{u} (ZMod n))]
variable [MonoidalPreadditive (ModuleCat.{u} (ZMod n))]
variable [∀ (K L : CochainComplex (ModuleCat.{u} (ZMod n)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ)]
variable [hModTensor :
    @DerivedTensor.Right.Has (ModuleCat.{u} (ZMod n)) _ _ _ _ _ _]
variable [MonoidalCategory
    (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [MonoidalPreadditive
    (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [∀ (K L : CochainComplex
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor
        (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n))))
      (ComplexShape.up ℤ)]
variable [hXYModTensor :
    @DerivedTensor.Right.Has
      (Sheaf (pullback X.hom Y.hom).smallEtaleTopology (ModuleCat.{u} (ZMod n)))
      _ _ _ _ _ _]
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

/-- Lemma 59.97.9: if `k` is a separably closed field, `X` and `Y` are finite type
schemes over `k`, and `n ≥ 1` is invertible in `k`, then for
`E ∈ D(X_étale, ZMod n)` and `K ∈ D(Y_étale, ZMod n)` one has
`RΓ(X ×_{Spec k} Y, pr₁⁻¹ E ⊗ᴸ pr₂⁻¹ K) ≅ RΓ(X, E) ⊗ᴸ RΓ(Y, K)`
in `D(ModuleCat (ZMod n))`. -/
@[stacks 0F1P]
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

end AlgebraicGeometry.Scheme.Etale

end
