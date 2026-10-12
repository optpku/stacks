/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.FieldTheory.Separable.Generated
public import stacks_project.Chap62.Lemma_62_5_1_Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injectivity and descent of families of cycles on fibres

This file records that base change of families of fibre cycles is injective
when every point of the base lifts along a residue-field-separable morphism,
and that a family on the base change descends uniquely when its two pullbacks
along `S' ×_S S'` agree.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace FiberCycleFamily

/-- Lemma 62.5.9 (1): if `f : X ⟶ S` is locally of finite type and every point
of `S` lifts along `g : S' ⟶ S` to a point whose residue-field extension is
separable, then base change of families of `r`-cycles on fibres along a
cartesian square is injective. -/
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

/-- Lemma 62.5.9 (2): in the setting of (1), a family of `r`-cycles on fibres of
`f' : X' ⟶ S'` is the unique base change of a family on `f : X ⟶ S` whenever
its pullbacks along the two projections of a self-fibre product of `g` agree. -/
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

end FiberCycleFamily
end AlgebraicGeometry.Scheme.Hom
