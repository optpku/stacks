/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_16_2_Hom
public import stacks_project.Chap99.Lemma_99_16_1
public import stacks_project.Chap76.Lemma_76_52_6_BaseChange

/-!
# Lemma 99.16.2: relative base convention

Local erratum: in the source's assumptions (1) and (2), `S` and `s ∈ S`
must be `Y` and a point of `Y`. The arbitrary base change is `V ⟶ Y`,
so relative perfectness and fibre vanishing are then relative to `V`.
This is the specialization `K = E` of Lemma 99.16.1 with vanishing locus
all of `Y`. The original uploaded source is preserved unchanged.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [Proper f] [Flat f] [FinitePresentation f]
variable (E : ModuleDerived X)

/-- Lemma 99.16.2 (1), local base erratum: a `Y`-perfect complex remains
`V`-perfect after arbitrary base change `V ⟶ Y`. -/
@[stacks 0DLD]
theorem isPerfectRelative_baseChange
    (hE : IsPerfectRelativeTo f E)
    {V : AlgebraicSpace S} (g : V ⟶ Y) :
    IsPerfectRelativeTo (Limits.pullback.snd f g) (baseChangePullback f g E) :=
  sorry

/-- Lemma 99.16.2 (2), local base erratum: negative self-Ext vanishing on
every field-valued fibre over `Y` persists on fibres over the new base `V`. -/
@[stacks 0DLD]
theorem fiberNegativeSelfExtVanish_baseChange
    (hE : IsPerfectRelativeTo f E)
    (h_vanish : ∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y)
    {V : AlgebraicSpace S} (g : V ⟶ Y) (v : FieldValuedPoint V) :
    fiberNegativeExtVanish (Limits.pullback.snd f g)
      (baseChangePullback f g E) (baseChangePullback f g E) v :=
  sorry

/-- Lemma 99.16.2 (3), local base erratum: all negative self-Ext groups vanish
after arbitrary base change for a `Y`-perfect complex with fibrewise vanishing. -/
@[stacks 0DLD]
theorem negativeSelfExt_eq_zero
    (hE : IsPerfectRelativeTo f E)
    (h_vanish : ∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y)
    {V : AlgebraicSpace S} (g : V ⟶ Y) (i : ℤ) (hi : i < 0) :
    Subsingleton (Ext⁽i⁾(baseChangePullback f g E, baseChangePullback f g E)) :=
  sorry

/-- Lemma 99.16.2 (4), local base erratum: the derived self-Hom functor of a
`Y`-perfect complex with negative fibre self-Ext vanishing is affine and of
finite presentation over `Y`. -/
@[stacks 0DLD]
theorem selfHomFunctorOver_isAffineFinitePresentation
    (hE : IsPerfectRelativeTo f E)
    (h_vanish : ∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y) :
    ∃ (F : AlgebraicSpace S) (π : F ⟶ Y),
      Affine π ∧ FinitePresentation π ∧
        Nonempty (selfHomFunctorOver f E ≅ yoneda.obj (Over.mk π)) :=
  sorry

/-- The corrected self-Hom representability assertion restricted to schemes
over `Y`; the relative perfectness and fibre vanishing are over `Y`. -/
theorem selfHomFunctor_isAffineFinitePresentation
    (hE : IsPerfectRelativeTo f E)
    (h_vanish : ∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y) :
    IsAffineFinitePresentationOver (selfHomFunctor f E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
