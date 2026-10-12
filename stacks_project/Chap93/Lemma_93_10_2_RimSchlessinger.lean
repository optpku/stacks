/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_16_11
public import stacks_project.Chap93.Example_93_10_1_Morphisms_of_schemes_Category

/-!
# Rim-Schlessinger condition for morphisms of schemes

The cofibered category `F` of pairs `(A, X ⟶ Y)` from Example 93.10.1 satisfies
(RS). Consequently each residue-fibre slice `Def_{X ⟶ Y}` is a deformation
category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeMorphismCat

/-- The slice projection `Def_{X ⟶ Y} ⥤ C_Λ` of Example 93.10.1. -/
abbrev deformationForget (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    deformation Λ k X Y f hX hY hf ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙ forget Λ k

/-- `deformationForget` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    deformationForget Λ k X Y f hX hY hf =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
        forget Λ k := sorry

/-- Example 93.10.1 satisfies the Rim-Schlessinger condition (RS). -/
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Λ k) := sorry

/-- The residue-fibre slice `Def_{X ⟶ Y}` is a deformation category. -/
instance instIsDeformationCategory_deformationForget
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    IsDeformationCategory (deformationForget Λ k X Y f hX hY hf) :=
  instIsDeformationCategory_overForget (forget Λ k) (residueObj Λ k X Y f hX hY hf)

end FlatSchemeMorphismCat
