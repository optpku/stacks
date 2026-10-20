/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.FieldTheory.Separable.Generated

/-!
# Injectivity and descent of families of cycles on fibres

Base change of families of fibre cycles is injective under surjective base
change. Families with equal pullbacks along compatible double-overlap
projections descend uniquely when every base point admits a lift with a
separable residue-field extension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiberCycleFamily

/-- Base change of families of fibre cycles along a cartesian square is
injective if every point of the base admits a lift with a separable
residue-field extension. -/
@[stacks 0H4X]
theorem baseChange_injective {S X S' X' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (hX' : IsPullback g' f' f g)
    (hsep : ∀ s : S, ∃ s' : S', g s' = s ∧
      Algebra.IsSeparableOver (S.residueField (g s')) (S'.residueField s'))
    {r : ℤ} :
    Function.Injective (fun α : f.FiberCycleFamily r ↦ baseChange hX' α) :=
  sorry

/-- Equality of families of fibre cycles after base change implies equality of
the original families, under the separable residue-field lift hypothesis. -/
theorem eq_of_baseChange_eq {S X S' X' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (hX' : IsPullback g' f' f g)
    (hsep : ∀ s : S, ∃ s' : S', g s' = s ∧
      Algebra.IsSeparableOver (S.residueField (g s')) (S'.residueField s'))
    {r : ℤ} {α₁ α₂ : f.FiberCycleFamily r}
    (hα : baseChange hX' α₁ = baseChange hX' α₂) : α₁ = α₂ :=
  sorry

/-- A family of fibre cycles whose pullbacks along compatible projections of
a self-fibre product agree descends uniquely if every base point admits a lift
with a separable residue-field extension. -/
@[stacks 0H4X]
theorem existsUnique_of_fst_baseChange_eq_snd
    {S X S' X' S'' X'' : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f']
    (hX' : IsPullback g' f' f g)
    (hsep : ∀ s : S, ∃ s' : S', g s' = s ∧
      Algebra.IsSeparableOver (S.residueField (g s')) (S'.residueField s'))
    {pr₁ pr₂ : S'' ⟶ S'} (hS'' : IsPullback pr₁ pr₂ g g)
    {p₁ p₂ : X'' ⟶ X'} {f'' : X'' ⟶ S''}
    (h₁ : IsPullback p₁ f'' f' pr₁) (h₂ : IsPullback p₂ f'' f' pr₂)
    (hprojection : p₁ ≫ g' = p₂ ≫ g')
    {r : ℤ} {α' : f'.FiberCycleFamily r}
    (hα' : baseChange h₁ α' = baseChange h₂ α') :
    ∃! α : f.FiberCycleFamily r, baseChange hX' α = α' :=
  sorry

/-- Base change of families of fibre cycles along a cartesian square is
injective whenever the morphism of bases is surjective. -/
theorem baseChange_injective_of_surjective {S X S' X' : Scheme.{u}}
    {f : X ⟶ S} [LocallyOfFiniteType f] {g : S' ⟶ S} [Surjective g]
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (hX' : IsPullback g' f' f g) {r : ℤ} :
    Function.Injective (fun α : f.FiberCycleFamily r ↦ baseChange hX' α) :=
  sorry

end AlgebraicGeometry.Scheme.Hom.FiberCycleFamily
