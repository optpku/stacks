module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap93.Lemma_93_9_8_Stalk

/-!
# Stalk functor of scheme deformation categories

Stacks 0DZM: a scheme `X` over `k` and a point `p` of `X` induce a natural
functor `Def_X ⟶ Def_{O_{X, p}}` of deformation categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Lemma 93.9.8
In Example 93.9.1 let `X` be a scheme over `k`. Let `p : X` be a point.
With `stalkDeformationCategory X hX p` as in Example 93.8.1, there is a
natural functor
`deformationCategory X hX ⥤ stalkDeformationCategory X hX p`
of deformation categories.
-/
@[stacks 0DZM]
abbrev stalkFunctor (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (p : X) :=
  FlatSchemeCat.stalkFunctor Λ k X hX p

/-- The object map of `stalkFunctor` sends a deformation `(A, Y)` of `X` to the
stalk pair `(A, Y.scheme.presheaf.stalk (schemeHom p))` over
`X.presheaf.stalk p`. -/
theorem stalkFunctor_obj_spec (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (p : X)
    (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    ((stalkFunctor Λ k X hX p).obj ξ).left = FlatSchemeCat.stalkObj X hX p ξ :=
  sorry

/-- Taking stalks of a deformation does not change the underlying object of `C_Λ`. -/
theorem stalkFunctor_comp_forget (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (p : X) :
    stalkFunctor Λ k X hX p ⋙
        Over.forget
            (Fiber.fiberInclusion.obj (FlatSchemeCat.residueStalkObj X hX p)) ⋙
          FlatAlgebraCat.forget =
      Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
        FlatSchemeCat.forget Λ k :=
  sorry

end
