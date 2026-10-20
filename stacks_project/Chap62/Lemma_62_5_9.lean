/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Descent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 62.5.9 (1): if `f : X ⟶ S` is locally of finite type and every point
of `S` lifts along `g : S' ⟶ S` to a point whose residue-field extension is
separable, then base change of families of `r`-cycles on fibres along a
cartesian square is injective. -/
@[stacks 0H4X] #check
  (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange_injective :
    ∀ {S X S' X' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (hX' : IsPullback g' f' f g)
    (hsep : ∀ s : S, ∃ s' : S', g s' = s ∧
      Algebra.IsSeparableOver (S.residueField (g s')) (S'.residueField s'))
    {r : ℤ},
    Function.Injective (fun α : f.FiberCycleFamily r ↦
      AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange hX' α))

/- Lemma 62.5.9 (2): in the setting of (1), a family of `r`-cycles on fibres of
`f' : X' ⟶ S'` is the unique base change of a family on `f : X ⟶ S` whenever
its pullbacks along the compatible projections of a self-fibre product of `g`
agree. -/
@[stacks 0H4X] #check
  (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.existsUnique_of_fst_baseChange_eq_snd :
    ∀ {S X S' X' S'' X'' : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f']
    (hX' : IsPullback g' f' f g)
    (hsep : ∀ s : S, ∃ s' : S', g s' = s ∧
      Algebra.IsSeparableOver (S.residueField (g s')) (S'.residueField s'))
    {pr₁ pr₂ : S'' ⟶ S'} (hS'' : IsPullback pr₁ pr₂ g g)
    {p₁ p₂ : X'' ⟶ X'} {f'' : X'' ⟶ S''}
    (h₁ : IsPullback p₁ f'' f' pr₁) (h₂ : IsPullback p₂ f'' f' pr₂)
    (hprojection : p₁ ≫ g' = p₂ ≫ g')
    {r : ℤ} {α' : f'.FiberCycleFamily r}
    (hα' : AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange h₁ α' =
      AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange h₂ α'),
    ∃! α : f.FiberCycleFamily r,
      AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange hX' α = α')
