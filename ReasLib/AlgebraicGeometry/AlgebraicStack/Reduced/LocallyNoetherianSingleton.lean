/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Reduced locally Noetherian singleton algebraic stacks

An algebraic stack over a scheme is reduced, locally Noetherian, and a
singleton on points if and only if it admits a locally finitely presented,
surjective, flat morphism from the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists a field `k` and a locally finitely presented, surjective, flat
morphism `GroupoidsOver.slice (Over.mk σ) ⟶ Z` from `Spec (.of k)`. -/
def existsLocallyOfFinitePresentationSurjectiveFlatSpecField {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] : Prop :=
  ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
    Groupoids.Hom.LocallyOfFinitePresentation f ∧ Groupoids.Hom.Surjective f ∧
      Groupoids.Hom.Flat f

namespace FieldCover

/-- The field-cover predicate is equivalent to the existence of a field and
a locally finitely presented, surjective, flat morphism from its spectrum. -/
theorem iff_locallyOfFinitePresentation {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ↔
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S)
        (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z),
        Groupoids.Hom.LocallyOfFinitePresentation f ∧
          Groupoids.Hom.Surjective f ∧ Groupoids.Hom.Flat f :=
  Iff.rfl

/-- A locally finitely presented, surjective, flat morphism from a field spectrum
witnesses the field-cover predicate. -/
theorem of_locallyOfFinitePresentation {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (f : GroupoidsOver.slice (Over.mk σ) ⟶ Z)
    [Groupoids.Hom.LocallyOfFinitePresentation f] [Groupoids.Hom.Surjective f]
    [Groupoids.Hom.Flat f] :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z :=
  ⟨k, inferInstance, σ, f, inferInstance, inferInstance, inferInstance⟩

end FieldCover

/-- An algebraic stack is reduced and locally Noetherian with a singleton space
of points if and only if it admits a locally finitely presented, surjective,
flat morphism from the spectrum of a field. -/
@[stacks 06MP]
theorem isReduced_isLocallyNoetherian_subsingleton_points_tfae {S : Scheme.{u}}
    (Z : GroupoidsOver S) [AlgebraicStack Z] :
    List.TFAE
      [ IsReduced Z ∧ IsLocallyNoetherian Z ∧ Nonempty (Points Z) ∧
          Subsingleton (Points Z)
      , existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ] :=
  sorry

namespace ReducedSingleton

/-- An algebraic stack is reduced, locally Noetherian, and a singleton on points
if and only if it admits a locally finitely presented, surjective, flat
morphism from the spectrum of a field. -/
theorem iff_locallyOfFinitePresentation_fieldCover
    {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z] :
    IsReduced Z ∧ IsLocallyNoetherian Z ∧ Nonempty (Points Z) ∧
        Subsingleton (Points Z) ↔
      existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z :=
  (isReduced_isLocallyNoetherian_subsingleton_points_tfae Z).out 0 1

/-- A locally finitely presented, surjective, flat field-spectrum cover exists
if and only if a field-valued point has these three morphism properties. -/
theorem locallyOfFinitePresentation_fieldCover_iff_fieldValuedPoint
    {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] :
    existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ↔
      ∃ p : FieldValuedPoint Z,
        Groupoids.Hom.LocallyOfFinitePresentation p.hom ∧
          Groupoids.Hom.Surjective p.hom ∧ Groupoids.Hom.Flat p.hom := by
  constructor
  · rintro ⟨k, field, σ, f, hf⟩
    exact ⟨FieldValuedPoint.of k σ f, hf⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.K, p.field, p.structureHom, p.hom, hp⟩

end ReducedSingleton

end AlgebraicGeometry.AlgebraicStack
