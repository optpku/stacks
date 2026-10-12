/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 62.5.8 (1): if `f : X ⟶ S` is locally of finite type, `g : S' ⟶ S` is
surjective, and `f' : X' ⟶ S'` is a base change of `f`, then a point of `X` of
residue-field transcendence degree `r` lifts to a point of `X'` of the same
transcendence degree. -/
@[stacks 0H4W] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.exists_point_residueFieldTrdegAt_eq_of_isPullback_of_surjective :
    ∀ {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) [Surjective g] (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (r : ℕ) (x : X)
    (hx : f.residueFieldTrdegAt x = r),
    ∃ x' : X', g' x' = x ∧ f'.residueFieldTrdegAt x' = r)

/- Lemma 62.5.8 (2): in the setting of (1), if `S''` is a fibre product of `g`
with itself and `f'' : X'' ⟶ S''` is a further base change of `f`, then any two
lifts of a residue-field transcendence degree `r` point of `X` to `X'` are the
images of a point of `X''` of the same transcendence degree. -/
@[stacks 0H4W] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.exists_point_residueFieldTrdegAt_eq_of_doublePullback :
    ∀ {S X S' X' S'' X'' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) [Surjective g] (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hX' : IsPullback g' f' f g) (pr₁ pr₂ : S'' ⟶ S')
    (hS'' : IsPullback pr₁ pr₂ g g) (p₁ p₂ : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (h₁ : IsPullback p₁ f'' f' pr₁) (h₂ : IsPullback p₂ f'' f' pr₂)
    (hprojection : p₁ ≫ g' = p₂ ≫ g')
    (r : ℕ) (x : X) (hx : f.residueFieldTrdegAt x = r)
    (x₁ x₂ : X') (hx₁ : g' x₁ = x) (hx₂ : g' x₂ = x)
    (htr₁ : f'.residueFieldTrdegAt x₁ = r)
    (htr₂ : f'.residueFieldTrdegAt x₂ = r),
    ∃ x'' : X'',
      p₁ x'' = x₁ ∧ p₂ x'' = x₂ ∧ f''.residueFieldTrdegAt x'' = r)
