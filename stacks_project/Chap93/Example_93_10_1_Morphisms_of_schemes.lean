module

public import stacks_project.Chap93.Example_93_10_1_Morphisms_of_schemes_Category
import StacksCheckRecall

/-!
# Deformation category of morphisms of schemes

Source-facing labeled entries for the category `F` of pairs `(A, X ⟶ Y)` with
both `X` and `Y` flat over `A` in `C_Λ`, the cofibered projection `p`, and
`Def_{X ⟶ Y} = F_{x0}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Example 93.10.1 (Morphisms of schemes) (1)
Let `F` be the category of pairs `(A, X ⟶ Y)` consisting of an object `A` of
`ArtinianLocalAlgCat Λ k` and a morphism `X ⟶ Y` of schemes over `A` with both
`X` and `Y` flat over `A`, with morphisms `(f, g, h) : (A', X' ⟶ Y') ⟶ (A, X ⟶ Y)`
given by `f : A' ⟶ A` in `ArtinianLocalAlgCat Λ k` together with `g : X ⟶ X'` and
`h : Y ⟶ Y'` making both squares of the displayed Spec-diagram cartesian. The
forgetful functor `p = FlatSchemeMorphismCat.forget` sends `(A, X ⟶ Y)` to `A`
and `(f, g, h)` to `f`. -/
@[stacks 0E3T]
abbrev flatSchemeMorphismCategory := FlatSchemeMorphismCat Λ k

/-- The forgetful functor of `flatSchemeMorphismCategory` sends `(A, X ⟶ Y)` to `A`. -/
theorem flatSchemeMorphismCategory_forget_obj (P : flatSchemeMorphismCategory Λ k) :
    (FlatSchemeMorphismCat.forget Λ k).obj P = P.base := sorry

/-- The forgetful functor of `flatSchemeMorphismCategory` sends `(f, g, h)` to `f`. -/
theorem flatSchemeMorphismCategory_forget_map
    {src tgt : flatSchemeMorphismCategory Λ k} (f : src ⟶ tgt) :
    (FlatSchemeMorphismCat.forget Λ k).map f = f.base := sorry

/- Example 93.10.1 (Morphisms of schemes) (2)
The functor `p : F ⥤ C_Λ` sending `(A, X ⟶ Y)` to `A` and `(f, g, h)` to `f` is
cofibered in groupoids. -/
@[stacks 0E3T]
#check (FlatSchemeMorphismCat.instIsFiberedInGroupoids_forget Λ k :
  IsFibered.InGroupoids (FlatSchemeMorphismCat.forget Λ k).op)

/-- Example 93.10.1 (Morphisms of schemes) (3)
Given a morphism of schemes `X ⟶ Y` over `k`, let `x0 = (k, X ⟶ Y)` be the
corresponding object of `F(k)`. The deformation category is the residue-fibre
slice `Def_{X ⟶ Y} = F_{x0} =
Over (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf))`. -/
@[stacks 0E3T]
abbrev deformation (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :=
  FlatSchemeMorphismCat.deformation Λ k X Y f hX hY hf

/-- `deformation` is the Over-slice of the residue-fibre object `x0 = (k, X ⟶ Y)`. -/
theorem deformation_spec (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    deformation Λ k X Y f hX hY hf =
      Over (Fiber.fiberInclusion.obj
        (FlatSchemeMorphismCat.residueObj Λ k X Y f hX hY hf)) := sorry
