/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Coverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine

/-!
# Affine coverings in the spaces-étale site

Affine covering families are spaces-étale covering families with affine members.
They exist over every object and refine every spaces-étale covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Morphisms in the spaces-étale site are étale as morphisms of algebraic spaces. -/
instance etale_spacesEtaleSite_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : spacesEtaleSite X} (f : U ⟶ V) : Etale f.left :=
  sorry

/-- A displayed family in `spacesEtaleSite X` is an affine covering when it covers in
`spacesEtalePrecoverage` and every member is an affine algebraic space. -/
def IsAffineCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {V : spacesEtaleSite X}
    {ι : Type u} (U : ι → spacesEtaleSite X) (f : ∀ i, U i ⟶ V) : Prop :=
  Presieve.ofArrows U f ∈ spacesEtalePrecoverage X V ∧ ∀ i, IsAffine (U i).left

/-- Affine covering families are exactly the spaces-étale covering families whose members
are affine algebraic spaces. -/
theorem isAffineCovering_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {V : spacesEtaleSite X}
    {ι : Type u} (U : ι → spacesEtaleSite X) (f : ∀ i, U i ⟶ V) :
    IsAffineCovering U f ↔
      Presieve.ofArrows U f ∈ spacesEtalePrecoverage X V ∧ ∀ i, IsAffine (U i).left :=
  Iff.rfl

/-- Every object of the spaces-étale site admits an affine covering family. -/
theorem exists_affineCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    (V : spacesEtaleSite X) :
    ∃ (ι : Type u) (_ : Small.{u} ι) (U : ι → spacesEtaleSite X) (f : ∀ i, U i ⟶ V),
      IsAffineCovering U f :=
  sorry

/-- Affine covering families are cofinal among spaces-étale coverings. -/
theorem exists_affineCovering_refinement {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V : spacesEtaleSite X} {ι : Type u} [Small.{u} ι] {W : ι → spacesEtaleSite X}
    (g : ∀ i, W i ⟶ V) (hg : Presieve.ofArrows W g ∈ spacesEtalePrecoverage X V) :
    ∃ (κ : Type u) (_ : Small.{u} κ) (U : κ → spacesEtaleSite X) (f : ∀ k, U k ⟶ V),
      IsAffineCovering U f ∧ (Presieve.ofArrows U f).FactorsThru (Presieve.ofArrows W g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
