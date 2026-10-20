/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Proper

/-!
# Towers of projective bundles

This module defines finite towers of represented projective bundles and records
their relative dimension and basic geometric properties.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

/-- An explicit finite tower whose steps are projective bundles of finite locally free
modules of positive constant rank. -/
inductive Tower : {P X : Scheme.{u}} → (P ⟶ X) → Type (u + 1) where
  /-- The empty tower over a scheme. -/
  | id (X : Scheme.{u}) : Tower (𝟙 X)
  /-- Add a projective bundle of a rank-`q + 1` module at the source of a tower. -/
  | prepend {P Y X : Scheme.{u}} (f : P ⟶ Y) (g : Y ⟶ X)
      (E : Y.Modules) (q : ℕ)
      [finiteLocallyFree : Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
      (representation : Representation f E) (tail : Tower g) : Tower (f ≫ g)

namespace Tower

/-- The sum of the relative dimensions of the projective-bundle steps in a tower. -/
def relativeDimension {P X : Scheme.{u}} {π : P ⟶ X} : Tower π → ℕ
  | .id _ => 0
  | @Tower.prepend _ _ _ _ _ _ q _ _ tail => q + relativeDimension tail

/-- The empty tower has relative dimension zero. -/
theorem relativeDimension_id (X : Scheme.{u}) :
    (Tower.id X).relativeDimension = 0 := sorry

/-- Prepending a rank-`q + 1` projective bundle adds `q` to relative dimension. -/
theorem relativeDimension_prepend {P Y X : Scheme.{u}} (f : P ⟶ Y) (g : Y ⟶ X)
    (E : Y.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (representation : Representation f E) (tail : Tower g) :
    (Tower.prepend f g E q representation tail).relativeDimension =
      q + tail.relativeDimension := sorry

/-- The one-step tower associated to a projective-bundle representation. -/
def single {P X : Scheme.{u}} (π : P ⟶ X) (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (representation : Representation π E) : Tower π :=
  (Category.comp_id π) ▸
    Tower.prepend π (𝟙 X) E q representation (Tower.id X)

/-- A one-step projective-bundle tower has the fiber dimension of its representation. -/
theorem relativeDimension_single {P X : Scheme.{u}} (π : P ⟶ X)
    (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (representation : Representation π E) :
    (single π E q representation).relativeDimension = q := sorry

/-- Concatenate two explicit projective-bundle towers. -/
def append {P Y X : Scheme.{u}} {f : P ⟶ Y} {g : Y ⟶ X} :
    Tower f → Tower g → Tower (f ≫ g)
  | .id _, T₂ => (Category.id_comp g).symm ▸ T₂
  | @Tower.prepend _ _ _ h f' E q _ representation tail, T₂ =>
      (Category.assoc h f' g).symm ▸
        Tower.prepend h (f' ≫ g) E q representation (append tail T₂)

/-- Relative dimensions add under concatenation of towers. -/
theorem relativeDimension_append {P Y X : Scheme.{u}} {f : P ⟶ Y} {g : Y ⟶ X}
    (T₁ : Tower f) (T₂ : Tower g) :
    (T₁.append T₂).relativeDimension =
      T₁.relativeDimension + T₂.relativeDimension := sorry

/-- The composite morphism represented by a projective-bundle tower is projective. -/
theorem projective {P X : Scheme.{u}} {π : P ⟶ X} (T : Tower π) :
    AlgebraicGeometry.Projective π := sorry

/-- The composite morphism represented by a projective-bundle tower is flat. -/
theorem flat {P X : Scheme.{u}} {π : P ⟶ X} (T : Tower π) :
    AlgebraicGeometry.Flat π := sorry

/-- The composite morphism represented by a projective-bundle tower is proper. -/
theorem isProper {P X : Scheme.{u}} {π : P ⟶ X} (T : Tower π) :
    AlgebraicGeometry.IsProper π := sorry

/-- A projective-bundle tower has the relative dimension computed by
`Tower.relativeDimension`. -/
theorem homRelativeDimension {P X : Scheme.{u}} {π : P ⟶ X} (T : Tower π) :
    Scheme.Hom.RelativeDimension π T.relativeDimension := sorry

/-- Composing a projective-bundle tower with a locally finite type morphism remains
locally of finite type. -/
theorem locallyOfFiniteTypeComp {S P X : Scheme.{u}} {π : P ⟶ X}
    (T : Tower π) (p : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType p] :
    AlgebraicGeometry.LocallyOfFiniteType (π ≫ p) := sorry

end Tower

end AlgebraicGeometry.Scheme.ProjectiveBundle
