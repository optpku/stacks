/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism
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

/- Example 93.10.1 (Morphisms of schemes) (1)
Let `F` be the category of pairs `(A, X ⟶ Y)` consisting of an object `A` of
`ArtinianLocalAlgCat Λ k` and a morphism `X ⟶ Y` of schemes over `A` with both
`X` and `Y` flat over `A`, with morphisms `(f, g, h) : (A', X' ⟶ Y') ⟶ (A, X ⟶ Y)`
given by `f : A' ⟶ A` in `ArtinianLocalAlgCat Λ k` together with `g : X ⟶ X'` and
`h : Y ⟶ Y'` making both squares of the displayed Spec-diagram cartesian. The
forgetful functor `p = FlatSchemeMorphismCat.forget` sends `(A, X ⟶ Y)` to `A`
and `(f, g, h)` to `f`. -/
@[stacks 0E3T]
#check (FlatSchemeMorphismCat Λ k : Type (u + 1))

#check (FlatSchemeMorphismCat.category (Λ := Λ) (k := k) :
  Category.{u} (FlatSchemeMorphismCat Λ k))

#check (FlatSchemeMorphismCat.forget Λ k :
  FlatSchemeMorphismCat Λ k ⥤ ArtinianLocalAlgCat Λ k)

#check (FlatSchemeMorphismCat.forget_obj Λ k :
  ∀ P : FlatSchemeMorphismCat Λ k, (FlatSchemeMorphismCat.forget Λ k).obj P = P.base)

#check (FlatSchemeMorphismCat.forget_map Λ k :
  ∀ {src tgt : FlatSchemeMorphismCat Λ k} (map : src ⟶ tgt),
    (FlatSchemeMorphismCat.forget Λ k).map map = map.base)

/- Example 93.10.1 (Morphisms of schemes) (2)
The functor `p : F ⥤ C_Λ` sending `(A, X ⟶ Y)` to `A` and `(f, g, h)` to `f` is
cofibered in groupoids. -/
@[stacks 0E3T]
#check (FlatSchemeMorphismCat.instIsFiberedInGroupoids_forget Λ k :
  IsFibered.InGroupoids (FlatSchemeMorphismCat.forget Λ k).op)

/- Example 93.10.1 (Morphisms of schemes) (3)
Given a morphism of schemes `X ⟶ Y` over `k`, let `x0 = (k, X ⟶ Y)` be the
corresponding object of `F(k)`. The deformation category is the residue-fibre
slice `Def_{X ⟶ Y} = F_{x0} =
Over (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf))`. -/
@[stacks 0E3T]
#check (FlatSchemeMorphismCat.deformation Λ k :
  ∀ (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k)),
    schemeMap ≫ hY = hX → Type (u + 1))

#check (FlatSchemeMorphismCat.deformation_spec Λ k :
  ∀ (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : schemeMap ≫ hY = hX),
    FlatSchemeMorphismCat.deformation Λ k X Y schemeMap hX hY hf =
      Over (Fiber.fiberInclusion.obj
        (FlatSchemeMorphismCat.residueObj Λ k X Y schemeMap hX hY hf)))
