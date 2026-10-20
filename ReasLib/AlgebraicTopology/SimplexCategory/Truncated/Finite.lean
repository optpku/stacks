/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Finite.Sigma
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite truncated simplex indexing categories

This module owns the finiteness data for truncated simplex categories and for the
structured and costructured arrow categories that compute their pointwise Kan extensions.
It is independent of a coefficient category and can be imported by both skeleton and
coskeleton constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace SimplexCategory

/-- Every two simplices admit a morphism, witnessed by a constant monotone map. -/
@[stacks 017M "nonempty simplex-category Hom-types"]
instance homNonempty (X Y : SimplexCategory) : Nonempty (X ⟶ Y) :=
  ⟨SimplexCategory.const X Y 0⟩

/-- Hom-types in the opposite simplex category are finite. -/
@[stacks 0183 "finite Hom-types in the opposite simplex category"]
instance opHomFinite (X Y : SimplexCategoryᵒᵖ) : Finite (X ⟶ Y) :=
  Finite.of_equiv (Y.unop ⟶ X.unop) Quiver.Hom.opEquiv

namespace Truncated

/-- Every two objects of a fixed truncated simplex category admit a morphism. -/
@[stacks 017M "nonempty truncated simplex-category Hom-types"]
instance homNonempty {m : ℕ} (X Y : SimplexCategory.Truncated m) : Nonempty (X ⟶ Y) :=
  ⟨ObjectProperty.homMk (SimplexCategory.const X.obj Y.obj 0)⟩

/-- The degree-`n` matching category for the `m`-coskeleton. -/
@[stacks 0183 "matching indexing category"]
abbrev matchingIndex (m n : ℕ) : Type :=
  StructuredArrow (op ⦋n⦌) (inclusion m).op

/-- Send an enumerating finite index to the corresponding truncated simplex object. -/
@[stacks 0183 "truncated simplex object enumeration map"]
def objEquiv.forward {m : ℕ} (i : Fin (m + 1)) : SimplexCategory.Truncated m :=
  ⟨SimplexCategory.mk i.1, Nat.le_of_lt_succ i.2⟩

/-- Recover the finite index of a truncated simplex object from its length. -/
@[stacks 0183 "truncated simplex object enumeration inverse"]
def objEquiv.inverse {m : ℕ} (X : SimplexCategory.Truncated m) : Fin (m + 1) :=
  ⟨X.obj.len, Nat.lt_succ_iff.mpr X.property⟩

/-- Recovering an index after constructing its truncated simplex object is the identity. -/
@[stacks 0183 "truncated simplex object enumeration left inverse"]
theorem objEquiv.left_inv {m : ℕ} (i : Fin (m + 1)) :
    objEquiv.inverse (objEquiv.forward i) = i := sorry

/-- Constructing an object after recovering its length index is the identity. -/
@[stacks 0183 "truncated simplex object enumeration right inverse"]
theorem objEquiv.right_inv {m : ℕ} (X : SimplexCategory.Truncated m) :
    objEquiv.forward (objEquiv.inverse X) = X := sorry

/-- The canonical enumeration of objects of the degree-`m` truncated simplex category. -/
@[stacks 0183 "truncated simplex object enumeration"]
def objEquiv (m : ℕ) : Fin (m + 1) ≃ SimplexCategory.Truncated m where
  toFun := objEquiv.forward
  invFun := objEquiv.inverse
  left_inv := objEquiv.left_inv
  right_inv := objEquiv.right_inv

/-- A truncated simplex category has finitely many objects. -/
@[stacks 0183 "finite objects in a truncated simplex category"]
instance finite (m : ℕ) : Finite (SimplexCategory.Truncated m) :=
  Finite.of_equiv (Fin (m + 1)) (objEquiv m)

/-- Hom-types in a truncated simplex category are finite. -/
@[stacks 0183 "finite Hom-types in a truncated simplex category"]
instance homFinite {m : ℕ} (X Y : SimplexCategory.Truncated m) : Finite (X ⟶ Y) := by
  refine Finite.of_injective (fun f => f.hom) ?_
  intro f g h
  exact ObjectProperty.hom_ext _ h

/-- A truncated simplex category is a finite category. -/
@[stacks 0183 "finite truncated simplex category"]
instance finCategory (m : ℕ) : FinCategory (SimplexCategory.Truncated m) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

namespace matchingIndex

/-- Build a matching-index object from its truncated target and structure map. -/
@[stacks 0183 "matching indexing object constructor"]
def objEquiv.forward {m n : ℕ}
    (p : Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
      (op ⦋n⦌ ⟶ (inclusion m).op.obj X)) : matchingIndex m n :=
  StructuredArrow.mk p.2

/-- Extract the truncated target and structure map of a matching-index object. -/
@[stacks 0183 "matching indexing object coordinates"]
def objEquiv.inverse {m n : ℕ} (A : matchingIndex m n) :
    Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
      (op ⦋n⦌ ⟶ (inclusion m).op.obj X) :=
  ⟨A.right, A.hom⟩

/-- Extracting matching-index coordinates after construction is the identity. -/
@[stacks 0183 "matching indexing object presentation left inverse"]
theorem objEquiv.left_inv {m n : ℕ}
    (p : Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
      (op ⦋n⦌ ⟶ (inclusion m).op.obj X)) :
    objEquiv.inverse (objEquiv.forward p) = p := sorry

/-- Reconstructing a matching-index object from its coordinates is the identity. -/
@[stacks 0183 "matching indexing object presentation right inverse"]
theorem objEquiv.right_inv {m n : ℕ} (A : matchingIndex m n) :
    objEquiv.forward (objEquiv.inverse A) = A := sorry

/-- The canonical presentation of a matching-index object by its truncated target and structure
map. -/
@[stacks 0183 "matching indexing object presentation"]
def objEquiv (m n : ℕ) :
    (Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
      (op ⦋n⦌ ⟶ (inclusion m).op.obj X)) ≃ matchingIndex m n where
  toFun := objEquiv.forward
  invFun := objEquiv.inverse
  left_inv := objEquiv.left_inv
  right_inv := objEquiv.right_inv

/-- The matching category for a truncated simplex category has finitely many objects. -/
@[stacks 0183 "matching indexing finite objects"]
instance finite (m n : ℕ) : Finite (matchingIndex m n) :=
  Finite.of_equiv _ (objEquiv m n)

/-- Hom-types in a matching category are finite. -/
@[stacks 0183 "matching indexing finite homs"]
instance homFinite {m n : ℕ} (A B : matchingIndex m n) : Finite (A ⟶ B) := by
  refine Finite.of_injective (fun f => f.right) ?_
  intro f g h
  exact StructuredArrow.hom_ext f g h

/-- The matching category for a truncated simplex category is a finite category. -/
@[stacks 0183 "matching indexing finite category"]
instance finCategory (m n : ℕ) : FinCategory (matchingIndex m n) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

end matchingIndex

namespace inclusion

namespace costructuredArrow

/-- Build a skeleton costructured-arrow object from its truncated source and structure map. -/
@[stacks 018N "skeleton costructured-arrow object constructor"]
def objEquiv.forward {m : ℕ} {Δ : SimplexCategory}
    (p : Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
      ((inclusion m).op.obj X ⟶ op Δ)) :
    CostructuredArrow (inclusion m).op (op Δ) :=
  CostructuredArrow.mk p.2

/-- Extract the truncated source and structure map of a skeleton costructured-arrow object. -/
@[stacks 018N "skeleton costructured-arrow object coordinates"]
def objEquiv.inverse {m : ℕ} {Δ : SimplexCategory}
    (A : CostructuredArrow (inclusion m).op (op Δ)) :
    Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
      ((inclusion m).op.obj X ⟶ op Δ) :=
  ⟨A.left, A.hom⟩

/-- Extracting skeleton costructured-arrow coordinates after construction is the identity. -/
@[stacks 018N "skeleton costructured-arrow presentation left inverse"]
theorem objEquiv.left_inv {m : ℕ} {Δ : SimplexCategory}
    (p : Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
      ((inclusion m).op.obj X ⟶ op Δ)) :
    objEquiv.inverse (objEquiv.forward p) = p := sorry

/-- Reconstructing a skeleton costructured-arrow object from its coordinates is the identity. -/
@[stacks 018N "skeleton costructured-arrow presentation right inverse"]
theorem objEquiv.right_inv {m : ℕ} {Δ : SimplexCategory}
    (A : CostructuredArrow (inclusion m).op (op Δ)) :
    objEquiv.forward (objEquiv.inverse A) = A := sorry

/-- The canonical presentation of a skeleton costructured-arrow object by its truncated source
and structure map. -/
@[stacks 018N "skeleton costructured-arrow object presentation"]
def objEquiv (m : ℕ) (Δ : SimplexCategory) :
    (Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
      ((inclusion m).op.obj X ⟶ op Δ)) ≃
      CostructuredArrow (inclusion m).op (op Δ) where
  toFun := objEquiv.forward
  invFun := objEquiv.inverse
  left_inv := objEquiv.left_inv
  right_inv := objEquiv.right_inv

/-- The costructured-arrow category used by the `m`-skeleton has finitely many objects. -/
@[stacks 018N "skeleton costructured-arrow finite objects"]
instance finite (m : ℕ) (Δ : SimplexCategory) :
    Finite (CostructuredArrow (inclusion m).op (op Δ)) :=
  Finite.of_equiv _ (objEquiv m Δ)

/-- Hom-types in the skeleton costructured-arrow category are finite. -/
@[stacks 018N "skeleton costructured-arrow finite homs"]
instance homFinite {m : ℕ} {Δ : SimplexCategory}
    (A B : CostructuredArrow (inclusion m).op (op Δ)) : Finite (A ⟶ B) := by
  refine Finite.of_injective (fun f => f.left) ?_
  intro f g h
  exact CostructuredArrow.hom_ext f g h

/-- The costructured-arrow category used by the `m`-skeleton is a finite category. -/
@[stacks 018N "skeleton costructured-arrow finite category"]
instance finCategory (m : ℕ) (Δ : SimplexCategory) :
    FinCategory (CostructuredArrow (inclusion m).op (op Δ)) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

end costructuredArrow
end inclusion

end Truncated

end SimplexCategory
