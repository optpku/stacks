/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 42.67.9 (1): compatibility of flat base change with dimension functions is
preserved by composition, and the shifts add. -/
@[stacks 0FVP]
#check (AlgebraicGeometry.Scheme.Hom.IsDimensionFunctionCompatible.comp :
  ∀ {S S' S'' : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S'] [UniversallyCatenary S'']
    (g : S' ⟶ S) [Flat g] (g' : S'' ⟶ S') [Flat g']
    (δ : S → ℤ) [IsDimensionFunction δ] (δ' : S' → ℤ) [IsDimensionFunction δ']
    (δ'' : S'' → ℤ) [IsDimensionFunction δ''] (c c' : ℤ),
    g.IsDimensionFunctionCompatible δ δ' c →
      g'.IsDimensionFunctionCompatible δ' δ'' c' →
        (g' ≫ g).IsDimensionFunctionCompatible δ δ'' (c + c'))

/- Lemma 42.67.9 (2): successive flat base-change pullbacks on cycles equal pullback along
the composite after the canonical pullback and grading transports. -/
@[stacks 0FVP]
#check (AlgebraicGeometry.CycleGroup.baseChangePullback_comp :
  ∀ {S S' S'' X : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S'] [UniversallyCatenary S'']
    (g : S' ⟶ S) [Flat g] (g' : S'' ⟶ S') [Flat g']
    (δ : S → ℤ) [IsDimensionFunction δ] (δ' : S' → ℤ) [IsDimensionFunction δ']
    (δ'' : S'' → ℤ) [IsDimensionFunction δ''] (c c' : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (hcompat' : g'.IsDimensionFunctionCompatible δ' δ'' c')
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ),
    (AlgebraicGeometry.CycleGroup.iteratedBaseChangeMap
          f g g' δ'' (add_assoc k c c')).comp
        ((AlgebraicGeometry.CycleGroup.baseChangePullback
              g' δ' δ'' c' hcompat' (pullback.snd f g) (k + c)).comp
          (AlgebraicGeometry.CycleGroup.baseChangePullback
            g δ δ' c hcompat f k)) =
      AlgebraicGeometry.CycleGroup.baseChangePullback
        (g' ≫ g) δ δ'' (c + c')
          (AlgebraicGeometry.Scheme.Hom.IsDimensionFunctionCompatible.comp
            g g' δ δ' δ'' c c' hcompat hcompat') f k)

/- Lemma 42.67.9 (3): successive flat base-change pullbacks on Chow groups equal pullback
along the composite after the canonical pullback and grading transports. -/
@[stacks 0FVP]
#check (AlgebraicGeometry.ChowGroup.baseChangePullback_comp :
  ∀ {S S' S'' X : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S'] [UniversallyCatenary S'']
    (g : S' ⟶ S) [Flat g] (g' : S'' ⟶ S') [Flat g']
    (δ : S → ℤ) [IsDimensionFunction δ] (δ' : S' → ℤ) [IsDimensionFunction δ']
    (δ'' : S'' → ℤ) [IsDimensionFunction δ''] (c c' : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (hcompat' : g'.IsDimensionFunctionCompatible δ' δ'' c')
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ),
    (AlgebraicGeometry.ChowGroup.iteratedBaseChangeMap
          f g g' δ'' (add_assoc k c c')).comp
        ((AlgebraicGeometry.ChowGroup.baseChangePullback
              g' δ' δ'' c' hcompat' (pullback.snd f g) (k + c)).comp
          (AlgebraicGeometry.ChowGroup.baseChangePullback
            g δ δ' c hcompat f k)) =
      AlgebraicGeometry.ChowGroup.baseChangePullback
        (g' ≫ g) δ δ'' (c + c')
          (AlgebraicGeometry.Scheme.Hom.IsDimensionFunctionCompatible.comp
            g g' δ δ' δ'' c c' hcompat hcompat') f k)
