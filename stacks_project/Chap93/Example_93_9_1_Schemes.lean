/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme
import StacksCheckRecall

/-!
# Deformation category of schemes

Source-facing labeled entries for the category `F` of pairs `(A, X)` with `X`
flat over `A` in `C_Λ`, the cofibered projection `p`, and `Def_X = F_{x0}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Example 93.9.1 (Schemes) (1)
Let `F` be the category of pairs `(A, X)` consisting of an object `A` of
`ArtinianLocalAlgCat Λ k` and a scheme `X` flat over `A`, with morphisms
`(f, g) : (B, Y) ⟶ (A, X)` given by `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k`
together with `g : X ⟶ Y` making a cartesian commutative Spec-square. The
forgetful functor `p = FlatSchemeCat.forget` sends `(A, X)` to `A` and
`(f, g)` to `f`. -/
@[stacks 0DY7]
#check (FlatSchemeCat Λ k : Type (u + 1))

#check (FlatSchemeCat.forget_obj Λ k :
  ∀ (P : FlatSchemeCat Λ k), (FlatSchemeCat.forget Λ k).obj P = P.base)
#check (FlatSchemeCat.forget_map Λ k :
  ∀ {src tgt : FlatSchemeCat Λ k} (f : src ⟶ tgt),
    (FlatSchemeCat.forget Λ k).map f = f.baseHom)

/- Example 93.9.1 (Schemes) (2)
The functor `p : F ⥤ C_Λ` sending `(A, X)` to `A` and `(f, g)` to `f` is
cofibered in groupoids. -/
@[stacks 0DY7]
#check (FlatSchemeCat.instIsFiberedInGroupoids_forget Λ k :
  IsFibered.InGroupoids (FlatSchemeCat.forget Λ k).op)

/- Example 93.9.1 (Schemes) (3)
Given a scheme `X` over `k`, let `x0 = (k, X)` be the corresponding object of
`F(k)`. The deformation category is the residue-fibre slice
`Def_X = F_{x0} = Over (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX))`. -/
@[stacks 0DY7]
#check (FlatSchemeCat.deformationCategory Λ k :
  ∀ (X : Scheme.{u}), (X ⟶ Spec (CommRingCat.of k)) → Type (u + 1))

#check (FlatSchemeCat.deformationCategory_spec Λ k :
  ∀ (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)),
    FlatSchemeCat.deformationCategory Λ k X hX =
      Over (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)))
