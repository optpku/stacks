/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.NaiveComparison.Explicit
import StacksCheckRecall

/-!
# Explicit comparison map to the naive cotangent complex

The standard resolution gives the face-difference comparison and its compatibility
with the inverse of the canonical derived comparison.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology
open CommRingCat.Under.CotangentComplex
open CommRingCat.Under.FreeAlgebra
open DerivedCategory.TStructure
open scoped Simplicial ZeroObject TensorProduct ChangeOfRings

universe u

noncomputable section

/- Remark 92.11.4. The explicit comparison of the standard resolution. -/
@[stacks 08UP] #check (Algebra.NaiveCotangent.toNaive :
  ∀ (A : CommRingCat.{u}) (B : Under A), obj A B ⟶ selfNaiveComplex A B)

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.toConormal_tmul :
  ∀ (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right),
    ((ModuleCat.extendRestrictScalarsAdj
          (standardAugmentation A B (op ⦋1⦌)).hom).homEquiv _ _
        (toConormal A B))
        (CommRingCat.KaehlerDifferential.d x) =
      (faceDifferenceDerivation A B).d x)

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.toConormal_tensor :
  ∀ (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) (b : B.right),
    toConormal A B
        (b ⊗ₜ[(standardTerm A B (op ⦋1⦌)).right,
          (standardAugmentation A B (op ⦋1⦌)).hom] (CommRingCat.KaehlerDifferential.d x)) =
      HSMul.hSMul (α := B.right) (β := naiveConormal A B B.right (selfHom A B)) b
        ((1 : B.right) ⊗ₜ[((functor A).obj B.right).right, (selfHom A B).right.hom]
          (faceSubCotangent A B x)))

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.faceDifferenceDerivation_apply :
  ∀ (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right),
    (faceDifferenceDerivation A B).d x =
      ((1 : B.right) ⊗ₜ[((functor A).obj B.right).right, (selfHom A B).right.hom]
        (faceSubCotangent A B x) :
        (ModuleCat.restrictScalars (standardAugmentation A B (op ⦋1⦌)).hom).obj
          (naiveConormal A B B.right (selfHom A B))))

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.toNaive_f_eq :
  ∀ (A : CommRingCat.{u}) (B : Under A) (i : ℤ),
    (toNaive A B).f i = toNaive_f A B i)

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.toNaive_f_zero :
  ∀ (A : CommRingCat.{u}) (B : Under A),
    (toNaive A B).f 0 =
      (objXIso A B 0).hom ≫
        selfDifferentials A B ≫
        (naiveComplex_X_zero A B B.right (selfHom A B)).inv)

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.toNaive_f_negOne :
  ∀ (A : CommRingCat.{u}) (B : Under A),
    (toNaive A B).f (-1) =
      (objXIso A B 1).hom ≫
        toConormal A B ≫
        (naiveComplex_X_negOne A B B.right (selfHom A B)).inv)

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.toNaive_f_negSucc_succ :
  ∀ (A : CommRingCat.{u}) (B : Under A) (n : ℕ),
    (toNaive A B).f (Int.negSucc (n + 1)) = 0)

#check (CategoryTheory.CommRingCat.Under.CotangentComplex.toNaive_f_pos :
  ∀ (A : CommRingCat.{u}) (B : Under A) (n : ℕ),
    (toNaive A B).f (Int.ofNat (n + 1)) = 0)

#check (Algebra.NaiveCotangent.toNaive_inv_toTruncGE_self :
  ∀ (A : CommRingCat.{u}) (B : Under A),
    (t.truncGE (-1)).map (DerivedCategory.Q.map (Algebra.NaiveCotangent.toNaive A B)) =
      inv (Algebra.NaiveCotangent.toTruncGE_self A B) ≫
        (t.truncGEπ (-1)).app (DerivedCategory.Q.obj (selfNaiveComplex A B)))
