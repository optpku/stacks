/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.RingHom

/-!
# Tensor-square multiplication

This leaf owns the canonical multiplication map of a tensor square.  Properties of the diagonal
map, such as flatness or Tor-amplitude, are stated against this map; consumers that need a chosen
algebra or module structure can use its `toAlgebra` or `targetModule` directly.

@stack 0FCW
@stack 0FCX
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v

namespace Algebra

/-- The multiplication homomorphism `B ⊗[A] B →+* B` of the tensor square. -/
@[stacks 0FCW "tensor-square multiplication",
  stacks 0FCX "tensor-square multiplication"]
def tensorSquareMultiplication
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    B ⊗[A] B →+* B :=
  (Algebra.TensorProduct.lmul' (S := B) A).toRingHom

/-- The algebra structure on `B` selected by tensor-square multiplication.

This named owner is retained for downstream code that must pin the map-induced
structure explicitly; theorem statements should prefer the map-level API when no
such structure is needed. -/
@[reducible, stacks 0FCW "tensor-square multiplication algebra owner",
  stacks 0FCX "tensor-square multiplication algebra owner"]
noncomputable def tensorSquareMultiplicationAlgebra
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    Algebra (B ⊗[A] B) B :=
  (tensorSquareMultiplication A B).toAlgebra

/-- The target of tensor-square multiplication as a module over the tensor square. -/
@[stacks 0FCW "tensor-square multiplication module owner",
  stacks 0FCX "tensor-square multiplication module owner"]
noncomputable def tensorSquareMultiplicationModule
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    ModuleCat (B ⊗[A] B) :=
  (tensorSquareMultiplication A B).targetModule

/-- The tensor-square multiplication map sends a pure tensor to the product of its factors.

This map-level rule is the preferred computational interface for consumers; it avoids exposing
the implementation through `Algebra.TensorProduct.lmul'`. -/
@[simp, stacks 0FCW "tensor-square multiplication computation",
  stacks 0FCX "tensor-square multiplication computation"]
theorem tensorSquareMultiplication.apply_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (b₁ b₂ : B) :
    tensorSquareMultiplication A B (b₁ ⊗ₜ[A] b₂) = b₁ * b₂ := by
  simp [tensorSquareMultiplication]

/-- Tensor-square multiplication is surjective; every `b : B` is the image of
`1 ⊗ b`. -/
@[stacks 092M "tensor-square multiplication is surjective"]
theorem tensorSquareMultiplication.surjective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] :
    Function.Surjective (tensorSquareMultiplication A B) := by
  intro b
  exact ⟨1 ⊗ₜ[A] b, by simp⟩

/-- Under the map-induced algebra structure, the pure tensor `b₁ ⊗ b₂` maps to `b₁ * b₂`.  The
local `letI` deliberately pins this noncanonical algebra structure: Mathlib does not install a
global algebra instance for a self-tensor product because the same carrier can have several
scalar actions. -/
@[simp, stacks 0FCW "map-induced algebra computation",
  stacks 0FCX "map-induced algebra computation"]
theorem tensorSquareMultiplication.algebraMap_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (b₁ b₂ : B) :
    -- Local instance justification (noncanonical choice): the tensor-square map selects the
    -- scalar action explicitly because no global self-tensor algebra instance is coherent.
    letI : Algebra (B ⊗[A] B) B := (tensorSquareMultiplication A B).toAlgebra
    algebraMap (B ⊗[A] B) B (b₁ ⊗ₜ[A] b₂) = b₁ * b₂ := by
  change tensorSquareMultiplication A B (b₁ ⊗ₜ[A] b₂) = b₁ * b₂
  exact tensorSquareMultiplication.apply_tmul b₁ b₂

/-- The tensor-square action on `B` multiplies the two tensor factors and then the module
element.  The local `letI` selects the same map-induced scalar action as the algebra formula. -/
@[simp, stacks 0FCW "map-induced module computation",
  stacks 0FCX "map-induced module computation"]
theorem tensorSquareMultiplication.smul_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (b₁ b₂ b₃ : B) :
    -- Local instance justification (noncanonical choice): this action is induced by the selected
    -- tensor-square multiplication map and must not become a competing global instance.
    letI : Algebra (B ⊗[A] B) B := (tensorSquareMultiplication A B).toAlgebra
    (b₁ ⊗ₜ[A] b₂) • b₃ = (b₁ * b₂) * b₃ := by
  change tensorSquareMultiplication A B (b₁ ⊗ₜ[A] b₂) * b₃ = (b₁ * b₂) * b₃
  rw [tensorSquareMultiplication.apply_tmul]

/-- Compatibility spelling for the pure-tensor computation through the named
map-induced algebra structure. -/
@[simp]
theorem tensorSquareMultiplicationAlgebra_algebraMap_tmul
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (b₁ b₂ : B) :
    -- Local instance justification (noncanonical choice): preserve the legacy explicit owner
    -- without registering its scalar action globally.
    letI : Algebra (B ⊗[A] B) B := tensorSquareMultiplicationAlgebra A B
    algebraMap (B ⊗[A] B) B (b₁ ⊗ₜ[A] b₂) = b₁ * b₂ := by
  change tensorSquareMultiplication A B (b₁ ⊗ₜ[A] b₂) = b₁ * b₂
  exact tensorSquareMultiplication.apply_tmul b₁ b₂

/-- Compatibility spelling for the tensor-square action through the named
map-induced algebra structure. -/
@[simp]
theorem tensorSquareMultiplicationModule_tmul_smul
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (b₁ b₂ b₃ : B) :
    -- Local instance justification (noncanonical choice): preserve the legacy explicit owner
    -- without registering its scalar action globally.
    letI : Algebra (B ⊗[A] B) B := tensorSquareMultiplicationAlgebra A B
    (b₁ ⊗ₜ[A] b₂) • b₃ = (b₁ * b₂) * b₃ := by
  change tensorSquareMultiplication A B (b₁ ⊗ₜ[A] b₂) * b₃ = (b₁ * b₂) * b₃
  rw [tensorSquareMultiplication.apply_tmul]

end Algebra
