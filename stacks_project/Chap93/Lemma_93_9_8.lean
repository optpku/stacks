module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Stalk
import StacksCheckRecall

/-!
# Stalk functor of scheme deformation categories

Stacks 0DZM: a scheme `X` over `k` and a point `p` of `X` induce a natural
functor `Def_X ⟶ Def_{O_{X, p}}` of deformation categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped BasedFunctor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
  [AlgebraicGeometry.Flat hX] (p : X)

/- Lemma 93.9.8
In Example 93.9.1 let `X` be a scheme over `k`. Let `p : X` be a point.
With `stalkDeformationCategory X hX p` as in Example 93.8.1, there is a
natural functor
`deformationCategory X hX ⥤ stalkDeformationCategory X hX p`
of deformation categories.
-/
@[stacks 0DZM] #check (FlatSchemeCat.stalkFunctor Λ k X hX p :
  FlatSchemeCat.deformationCategory Λ k X hX ⥤
    FlatSchemeCat.stalkDeformationCategory X hX p)

#check (FlatSchemeCat.stalkFunctor_obj_left X hX p :
  ∀ (ξ : FlatSchemeCat.deformationCategory Λ k X hX),
    ((FlatSchemeCat.stalkFunctor Λ k X hX p).obj ξ).left =
      FlatSchemeCat.stalkObj X hX p ξ)

#check (FlatSchemeCat.stalkFunctor_comp_forget X hX p :
  FlatSchemeCat.stalkFunctor Λ k X hX p ⋙
      Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueStalkObj X hX p)) ⋙
        FlatAlgebraCat.forget =
    Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
      FlatSchemeCat.forget Λ k)

#check (FlatSchemeCat.stalkBasedFunctor Λ k X hX p :
  BasedCategory.ofFunctor
      (Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
        FlatSchemeCat.forget Λ k) ⥤ᵇ
    BasedCategory.ofFunctor
      (Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueStalkObj X hX p)) ⋙
        FlatAlgebraCat.forget))

end
