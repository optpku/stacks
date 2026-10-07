module

public import stacks_project.Chap93.Example_93_9_1_Schemes_Category
public import stacks_project.Chap93.Example_93_9_1_Schemes_Deformation
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

/-- Example 93.9.1 (Schemes) (1)
Let `F` be the category of pairs `(A, X)` consisting of an object `A` of
`ArtinianLocalAlgCat Λ k` and a scheme `X` flat over `A`, with morphisms
`(f, g) : (B, Y) ⟶ (A, X)` given by `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k`
together with `g : X ⟶ Y` making a cartesian commutative Spec-square. The
forgetful functor `p = FlatSchemeCat.forget` sends `(A, X)` to `A` and
`(f, g)` to `f`. -/
@[stacks 0DY7]
abbrev flatSchemeCategory := FlatSchemeCat Λ k

/-- The forgetful functor of `flatSchemeCategory` sends `(A, X)` to `A`. -/
theorem flatSchemeCategory_forget_obj (P : flatSchemeCategory Λ k) :
    (FlatSchemeCat.forget Λ k).obj P = P.base := sorry

/-- The forgetful functor of `flatSchemeCategory` sends `(f, g)` to `f`. -/
theorem flatSchemeCategory_forget_map {src tgt : flatSchemeCategory Λ k} (f : src ⟶ tgt) :
    (FlatSchemeCat.forget Λ k).map f = f.baseHom := sorry

/- Example 93.9.1 (Schemes) (2)
The functor `p : F ⥤ C_Λ` sending `(A, X)` to `A` and `(f, g)` to `f` is
cofibered in groupoids. -/
@[stacks 0DY7]
#check (FlatSchemeCat.instIsFiberedInGroupoids_forget Λ k :
  IsFibered.InGroupoids (FlatSchemeCat.forget Λ k).op)

/-- Example 93.9.1 (Schemes) (3)
Given a scheme `X` over `k`, let `x0 = (k, X)` be the corresponding object of
`F(k)`. The deformation category is the residue-fibre slice
`Def_X = F_{x0} = Over (Fiber.fiberInclusion.obj (residueObj Λ k X hX))`. -/
@[stacks 0DY7]
abbrev deformationCategory (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :=
  FlatSchemeCat.deformationCategory Λ k X hX

/-- `deformationCategory` is the Over-slice of the residue-fibre object `x0 = (k, X)`. -/
theorem deformationCategory_spec (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    deformationCategory Λ k X hX =
      Over (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) := sorry
