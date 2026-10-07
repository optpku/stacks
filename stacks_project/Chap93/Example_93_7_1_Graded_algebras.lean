module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import stacks_project.Chap93.Example_93_7_1_Graded_algebras_Algebra
public import stacks_project.Chap93.Example_93_7_1_Graded_algebras_Category

/-!
# Deformation category of a graded algebra

The category `F` of pairs `(A, P)` and the residue-fibre slice
`Def_P = F_{x0}` of Example 93.7.1.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Example 93.7.1 (Graded algebras) (1)
Let `F` be the category of pairs `(A, P)` consisting of an object `A` of
`ArtinianLocalAlgCat Λ k` and a commutative `ℕ`-graded `A`-algebra `P` such that
each homogeneous piece `P.grading d` is a finite projective `A`-module, with
morphisms `(f, g) : (B, Q) ⟶ (A, P)` given by `f : B ⟶ A` in
`ArtinianLocalAlgCat Λ k` together with an `f`-linear graded map `g : Q → P`
inducing an isomorphism `Q ⊗_{B, f} A ≅ P` via `canonicalTensorMap`. The
forgetful functor `p = FiniteProjectiveGradedAlgebraCat.forget` sends `(A, P)`
to `A` and `(f, g)` to `f`, and is cofibered in groupoids. -/
@[stacks 0D3L]
abbrev gradedAlgebraCategory := FiniteProjectiveGradedAlgebraCat Λ k

/-- The forgetful functor of `gradedAlgebraCategory` sends `(A, P)` to `A`. -/
theorem gradedAlgebraCategory_forget_obj (X : gradedAlgebraCategory Λ k) :
    FiniteProjectiveGradedAlgebraCat.forget.obj X = X.base := sorry

/-- The forgetful functor of `gradedAlgebraCategory` sends `(f, g)` to `f`. -/
theorem gradedAlgebraCategory_forget_map {Q P : gradedAlgebraCategory Λ k} (f : Q ⟶ P) :
    FiniteProjectiveGradedAlgebraCat.forget.map f = f.baseHom := sorry

namespace FiniteProjectiveGradedAlgebraCat

/-- Example 93.7.1 (Graded algebras) (2)
Given a commutative `ℕ`-graded `k`-algebra `P` with `Module.Finite k (P.grading d)`
for all `d`, let `x0 = (k, P)` be the corresponding object of the fibre
`F(k)`. The deformation category is the residue-fibre slice
`Def_P = F_{x0} = Over (Fiber.fiberInclusion.obj (residueObj Λ P))`. -/
@[stacks 0D3L]
abbrev deformationCategory (P : FiniteProjectiveGradedAlgebra k) :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ P))

/-- `deformationCategory P` is the Over-slice of the residue-fibre object `x0 = (k, P)`. -/
theorem deformationCategory_spec (P : FiniteProjectiveGradedAlgebra k) :
    deformationCategory Λ k P = Over (Fiber.fiberInclusion.obj (residueObj Λ P)) := sorry

end FiniteProjectiveGradedAlgebraCat
