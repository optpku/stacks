module

public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_16_11
public import stacks_project.Chap93.Example_93_11_1_Algebraic_spaces_Deformation

/-!
# Rim-Schlessinger condition for algebraic spaces

The cofibered category `F` of pairs `(A, X)` from Example 93.11.1 satisfies
(RS). Consequently each residue-fibre slice `Def_X` is a deformation
category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraicSpaceCat

/-- The slice projection `Def_X ⥤ C_Λ` of Example 93.11.1. -/
abbrev deformationForget (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    deformation Λ k X ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X)) ⋙ forget Λ k

/-- `deformationForget` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    deformationForget Λ k X =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X)) ⋙ forget Λ k := sorry

/-- Example 93.11.1 satisfies the Rim-Schlessinger condition (RS). -/
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Λ k) := sorry

/-- The residue-fibre slice `Def_X` is a deformation category. -/
instance instIsDeformationCategory_deformationForget
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    IsDeformationCategory (deformationForget Λ k X) :=
  instIsDeformationCategory_overForget (forget Λ k) (residueObj Λ k X)

end FlatAlgebraicSpaceCat
