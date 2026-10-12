/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.GradedAlgebra.FiniteProjective
public import ReasLib.AlgebraicGeometry.FormalDeformation.GradedAlgebra
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation

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

/- Example 93.7.1 (Graded algebras) (1)
Let `F` be the category of pairs `(A, P)` consisting of an object `A` of
`ArtinianLocalAlgCat Λ k` and a commutative `ℕ`-graded `A`-algebra `P` such that
each homogeneous piece `P.grading d` is a finite projective `A`-module, with
morphisms `(f, g) : (B, Q) ⟶ (A, P)` given by `f : B ⟶ A` in
`ArtinianLocalAlgCat Λ k` together with an `f`-linear graded map `g : Q → P`
inducing an isomorphism `Q ⊗_{B, f} A ≅ P` via `canonicalTensorMap`. The
forgetful functor `p = FiniteProjectiveGradedAlgebraCat.forget` sends `(A, P)`
to `A` and `(f, g)` to `f`, and is cofibered in groupoids. -/
@[stacks 0D3L] #check (FiniteProjectiveGradedAlgebraCat Λ k : Type (u + 1))

#check (FiniteProjectiveGradedAlgebraCat.forget :
  FiniteProjectiveGradedAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)

#check (FiniteProjectiveGradedAlgebraCat.forget_obj :
  ∀ X : FiniteProjectiveGradedAlgebraCat Λ k,
    FiniteProjectiveGradedAlgebraCat.forget.obj X = X.base)

#check (FiniteProjectiveGradedAlgebraCat.forget_map :
  ∀ {Q P : FiniteProjectiveGradedAlgebraCat Λ k} (f : Q ⟶ P),
    FiniteProjectiveGradedAlgebraCat.forget.map f = f.baseHom)

#check (FiniteProjectiveGradedAlgebraCat.instIsFiberedInGroupoids_forget :
  IsFibered.InGroupoids
    (FiniteProjectiveGradedAlgebraCat.forget :
      FiniteProjectiveGradedAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).op)

/- Example 93.7.1 (Graded algebras) (2)
Given a commutative `ℕ`-graded `k`-algebra `P` with `Module.Finite k (P.grading d)`
for all `d`, let `x0 = (k, P)` be the corresponding object of the fibre
`F(k)`. The deformation category is the residue-fibre slice
`Def_P = F_{x0} = Over (Fiber.fiberInclusion.obj (residueObj Λ P))`. -/
@[stacks 0D3L] #check (FiniteProjectiveGradedAlgebraCat.deformationCategory Λ k :
  FiniteProjectiveGradedAlgebra k → Type (u + 1))

#check (FiniteProjectiveGradedAlgebraCat.ofResidue Λ :
  FiniteProjectiveGradedAlgebra k → FiniteProjectiveGradedAlgebraCat Λ k)

#check (FiniteProjectiveGradedAlgebraCat.residueObj Λ :
  FiniteProjectiveGradedAlgebra k →
    FiniteProjectiveGradedAlgebraCat.forget.Fiber (ArtinianLocalAlgCat.residue Λ k))

#check (FiniteProjectiveGradedAlgebraCat.deformationCategory_spec Λ k :
  ∀ P : FiniteProjectiveGradedAlgebra k,
    FiniteProjectiveGradedAlgebraCat.deformationCategory Λ k P =
      Over (Fiber.fiberInclusion.obj (FiniteProjectiveGradedAlgebraCat.residueObj Λ P)))
