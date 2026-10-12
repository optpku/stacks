/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Example_93_8_1_Rings_Category

/-!
# Deformation category of a ring

The category `F` of pairs `(A, P)` and the residue-fibre slice
`Def_P = F_{x0}` of Example 93.8.1.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Example 93.8.1 (Rings) (1)
Let `F` be the category of pairs `(A, P)` consisting of an object `A` of
`ArtinianLocalAlgCat Λ k` and a flat `A`-algebra `P`, with morphisms
`(f, g) : (B, Q) ⟶ (A, P)` given by `f : B ⟶ A` in
`ArtinianLocalAlgCat Λ k` together with an `f`-linear ring map `g : Q → P`
inducing an isomorphism `Q ⊗_{B, f} A ≅ P` via `canonicalTensorMap`. The
forgetful functor `p = FlatAlgebraCat.forget` sends `(A, P)` to `A` and
`(f, g)` to `f`, and is cofibered in groupoids. -/
@[stacks 0DY1]
abbrev flatAlgebraCategory := FlatAlgebraCat Λ k

/-- The forgetful functor of `flatAlgebraCategory` sends `(A, P)` to `A`. -/
theorem flatAlgebraCategory_forget_obj (X : flatAlgebraCategory Λ k) :
    FlatAlgebraCat.forget.obj X = X.base := sorry

/-- The forgetful functor of `flatAlgebraCategory` sends `(f, g)` to `f`. -/
theorem flatAlgebraCategory_forget_map {Q P : flatAlgebraCategory Λ k} (f : Q ⟶ P) :
    FlatAlgebraCat.forget.map f = f.baseHom := sorry

/-- Example 93.8.1 (Rings) (2)
Given a `k`-algebra `P`, let `x0 = (k, P)` be the corresponding object of the
fibre `F(k)`. The deformation category is the residue-fibre slice
`Def_P = F_{x0} = Over (Fiber.fiberInclusion.obj (residueObj Λ P))`. -/
@[stacks 0DY1]
abbrev deformationCategory (P : Type u) [CommRing P] [Algebra k P] :=
  FlatAlgebraCat.deformationCategory Λ k P

/-- `deformationCategory P` is the Over-slice of the residue-fibre object `x0 = (k, P)`. -/
theorem deformationCategory_spec (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P =
      Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P)) := sorry
