/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.RingTheory.Catenary.Field

/-!
# Composition of proper pushforwards on cycle groups

This file records functoriality of proper pushforward on relative cycle groups.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Proper pushforward on relative cycle groups is compatible with composition. -/
theorem mapHom_comp_of_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y Z : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f.left] [IsProper g.left] (k : ℤ) :
    (mapHom g.left (Y.hom.relativeDimensionFunction δ)
      (Z.hom.relativeDimensionFunction δ) k).comp
        (mapHom f.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) k) =
      mapHom (f.left ≫ g.left) (X.hom.relativeDimensionFunction δ)
        (Z.hom.relativeDimensionFunction δ) k := sorry

/-- Proper pushforward on cycle groups of varieties over a field is compatible with
composition. -/
theorem mapHom_comp_of_proper_over_field {K : Type u} [Field K]
    (X Y Z : SchemeOverField K) [Variety X] [Variety Y] [Variety Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f.left] [IsProper g.left] (k : ℤ) :
    (mapHom g.left
      (Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
      (Z.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)) k).comp
        (mapHom f.left
          (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
          (Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)) k) =
      mapHom (f.left ≫ g.left)
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (Z.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)) k := sorry

end AlgebraicGeometry.CycleGroup
