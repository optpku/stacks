/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Factorizations through morphisms of finite presentation

This module relates factorizations through closed immersions and morphisms of finite
presentation to quasi-compactness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/-- A morphism that factors as a closed immersion followed by a morphism of finite
presentation is quasi-compact. -/
theorem closedImmersion_comp_le_quasiCompact :
    (MorphismProperty.comp @IsClosedImmersion
      (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme)) ≤ @QuasiCompact := by
  intro X Y f hf
  rcases hf with ⟨fac⟩
  rw [← fac.fac]
  exact @quasiCompact_comp X fac.Z Y fac.i fac.p
    fac.hi.quasiCompact fac.hp.toQuasiCompact

/-- A locally finite type morphism from a quasi-compact and quasi-separated scheme factors
as an immersion followed by a morphism of finite presentation. -/
theorem exists_immersion_factorization_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier] :
    (MorphismProperty.comp @IsImmersion
      (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme)) f := sorry

/-- A locally finite type morphism from a quasi-compact and quasi-separated scheme to a
quasi-separated scheme factors as a closed immersion followed by a morphism of finite
presentation. -/
theorem exists_closedImmersion_factorization_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    [QuasiSeparatedSpace S.carrier] :
    (MorphismProperty.comp @IsClosedImmersion
      (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme)) f := sorry

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
