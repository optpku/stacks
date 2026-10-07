module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap93.Lemma_93_9_6_Restrict

/-!
# Restriction functor of scheme deformation categories
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Lemma 93.9.6
In Example 93.9.1 let `X` be a scheme over `k`. Let `U ⊂ X` be an open
subscheme. There is a natural functor
`deformationCategory Λ k X hX ⥤ᵇ
deformationCategory Λ k U.toScheme (U.ι ≫ hX)`
of deformation categories, sending a deformation `(A, Y)` of `X` to the
corresponding open of `Y` as a deformation of `U`. -/
@[stacks 0DYW]
abbrev restrictOpen (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens) :=
  FlatSchemeCat.restrictOpen Λ k X hX U

/-- The restriction functor of deformation categories lies strictly over
`ArtinianLocalAlgCat`. -/
theorem restrictOpen_comp_forget (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens) :
    (restrictOpen Λ k X hX U).toFunctor ⋙
        Over.forget (Fiber.fiberInclusion.obj
            (FlatSchemeCat.residueObj Λ k U.toScheme (U.ι ≫ hX))) ⋙
          FlatSchemeCat.forget Λ k =
      Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
        FlatSchemeCat.forget Λ k :=
  sorry

end
