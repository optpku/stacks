/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PontryaginDual.Right

/-!
# Differential graded balanced pairings

The reusable content of the tensor-character adjunction can be expressed without choosing a
presentation of the balanced tensor product: a DG-balanced pairing is precisely a morphism into
the Pontryagin dual.  A tensor-product owner can use this as its universal-property target.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R}

/-- The homogeneous linear-map type underlying a differential graded balanced pairing.  Naming
this type fixes the canonical `R`-action on the character module uniformly, including for
`R = ℤ`, where another propositionally equal module structure is also available. -/
abbrev BalancedPairing.Component (N : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, w} A) (p : ℤ) :=
  N.X p →ₗ[R] CharacterModule (M.X (-p))

/-- A differential graded `A`-balanced pairing between a right DG module `N` and a left DG
module `M`, valued in `ℚ/ℤ`.  The character-valued family keeps both balance and differential
compatibility available to tensor and duality consumers. -/
@[stacks 09K3 "differential graded balanced pairings"]
structure BalancedPairing (N : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, w} A) where
  /-- The character-valued pairing in each complementary degree. -/
  hom (p : ℤ) : BalancedPairing.Component N M p
  /-- Compatibility with the differentials on `N` and the character dual of `M`. -/
  comm_d (p : ℤ) (x : N.X p) :
    hom (p + 1) (N.d p x) =
      LeftDifferentialGradedModule.pontryaginDualD M p (hom p x)
  /-- The right action on `N` is balanced with the left action on `M`. -/
  balance (p i : ℤ) (x : N.X p) (a : A.X i) :
    hom (p + i) (N.smul p i x a) =
      LeftDifferentialGradedModule.pontryaginDualSmulValue M p i (hom p x) a

namespace BalancedPairing

/-- Evaluate a DG-balanced pairing on homogeneous elements of complementary degrees. -/
def eval {N : DifferentialGradedModule.{u, v} A}
    {M : LeftDifferentialGradedModule.{u, w} A} (b : BalancedPairing N M)
    (p : ℤ) (x : N.X p) (y : M.X (-p)) : AddCircle (1 : ℚ) :=
  b.hom p x y

/-- DG-balanced pairings are determined by their values on homogeneous elements. -/
@[ext]
theorem ext {N : DifferentialGradedModule.{u, v} A}
    {M : LeftDifferentialGradedModule.{u, w} A} {b c : BalancedPairing N M}
    (h : ∀ (p : ℤ) (x : N.X p) (y : M.X (-p)), b.eval p x y = c.eval p x y) :
    b = c := sorry

/-- Regard a morphism into a Pontryagin dual as its associated DG-balanced pairing. -/
def ofHom {N : DifferentialGradedModule.{u, v} A}
    {M : LeftDifferentialGradedModule.{u, w} A}
    (f : DifferentialGradedModule.Hom N
      (LeftDifferentialGradedModule.pontryaginDual M)) : BalancedPairing N M where
  hom := f.hom
  comm_d := sorry
  balance := sorry

/-- A DG-balanced pairing defines the corresponding morphism into a Pontryagin dual. -/
def toHom {N : DifferentialGradedModule.{u, v} A}
    {M : LeftDifferentialGradedModule.{u, w} A} (b : BalancedPairing N M) :
    DifferentialGradedModule.Hom N
      (LeftDifferentialGradedModule.pontryaginDual M) where
  hom := b.hom
  comm_d := sorry
  comm_smul := sorry

/-- Lemma 22.19.2 (09K3): morphisms from a right DG module `N` into the Pontryagin dual of a
left DG module `M` are canonically equivalent to DG `A`-balanced pairings `N × M ⟶ ℚ/ℤ`. -/
@[stacks 09K3]
def homEquiv (N : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, w} A) :
    DifferentialGradedModule.Hom N
      (LeftDifferentialGradedModule.pontryaginDual M) ≃ BalancedPairing N M where
  toFun := ofHom
  invFun := toHom
  left_inv := sorry
  right_inv := sorry

/-- The forward dual-Hom equivalence retains the original homogeneous maps. -/
@[simp]
theorem homEquiv_hom (N : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, w} A)
    (f : DifferentialGradedModule.Hom N
      (LeftDifferentialGradedModule.pontryaginDual M)) (p : ℤ) :
    (homEquiv N M f).hom p = f.hom p := sorry

/-- The inverse dual-Hom equivalence retains the pairing's homogeneous maps. -/
@[simp]
theorem homEquiv_symm_hom (N : DifferentialGradedModule.{u, v} A)
    (M : LeftDifferentialGradedModule.{u, w} A) (b : BalancedPairing N M) (p : ℤ) :
    ((homEquiv N M).symm b).hom p = b.hom p := sorry

end BalancedPairing

end DifferentialGradedModule
