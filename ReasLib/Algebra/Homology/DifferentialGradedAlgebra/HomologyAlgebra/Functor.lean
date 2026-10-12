/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Commutative.Category
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyAlgebra

/-!
# Homology of strictly commutative chain DGAs

This file assembles the canonical nonnegative graded homology algebra and its existing induced
morphisms into a functor. The construction is independent of divided powers.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace ChainDGAlgebra.Strict

variable {R : Type u} [CommRing R]

/-- Canonical nonnegative graded homology is functorial on strictly commutative chain DGAs. -/
@[stacks 09PK "infrastructure: homology of strictly commutative chain DGAs"]
noncomputable def homology (R : Type u) [CommRing R] :
    ChainDGAlgebra.Strict.{u, v} R ⥤ NonnegGradedAlgebra.{u, v} R where
  obj A := A.toChainDGAlgebra.homologyNonnegativePart
  map f := ChainDGAlgebra.Hom.homologyHom f
  map_id A := ChainDGAlgebra.Hom.homologyHom_id A.toChainDGAlgebra
  map_comp f g := ChainDGAlgebra.Hom.homologyHom_comp g f

/-- The homology functor sends a strict chain DGA to its canonical nonnegative homology
algebra. -/
@[simp] theorem homology_obj (A : ChainDGAlgebra.Strict.{u, v} R) :
    (homology R).obj A = A.toChainDGAlgebra.homologyNonnegativePart := sorry

/-- A homogeneous piece of the homology functor is the corresponding canonical homology
module. -/
@[simp] theorem homology_obj_piece (A : ChainDGAlgebra.Strict.{u, v} R) (n : ℕ) :
    ((homology R).obj A).piece n = A.toChainDGAlgebra.homologyPiece n := sorry

/-- The homology functor maps a chain-DGA homomorphism by its canonical graded homology map. -/
@[simp] theorem homology_map {A B : ChainDGAlgebra.Strict.{u, v} R} (f : A ⟶ B) :
    (homology R).map f = ChainDGAlgebra.Hom.homologyHom f := sorry

/-- The degree-`n` action of the homology functor is the canonical homology linear map. -/
@[simp] theorem homology_map_apply {A B : ChainDGAlgebra.Strict.{u, v} R}
    (f : A ⟶ B) (n : ℕ) (x : A.toChainDGAlgebra.homologyPiece n) :
    ((homology R).map f).map n x = ChainDGAlgebra.Hom.homologyLinearMap f n x := sorry

end ChainDGAlgebra.Strict
