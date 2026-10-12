/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_35_4_OpenRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Base-changed immersion-smooth factorizations

Given an immersion-smooth factorization of an `S`-morphism and a cartesian square, the
induced map into the pullback of the smooth factor is the base-changed immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The two paths around a cartesian square agree after inserting an immersion-smooth
factorization of the unprimed vertical map. -/
theorem gysinBaseChangeImmersion_comm
    {S : Scheme.{u}} {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f) :
    f'.left ≫ g.left = (g'.left ≫ i.left) ≫ h.left := sorry

/-- The comparison from `X'` into the pullback of `h` along `g` respects the structure
maps to `S`. -/
theorem gysinBaseChangeImmersion_over
    {S : Scheme.{u}} {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f) :
    pullback.lift f'.left (g'.left ≫ i.left)
        (gysinBaseChangeImmersion_comm square i h hfac) ≫
      (OpenRestriction.baseChange h g).hom = X'.hom := sorry

/-- The base-changed immersion `i' : X' ⟶ P'` induced by an immersion-smooth factorization
of `f` and a cartesian square. -/
noncomputable def gysinBaseChangeImmersion
    {S : Scheme.{u}} {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f) :
    X' ⟶ OpenRestriction.baseChange h g :=
  Over.homMk
    (pullback.lift f'.left (g'.left ≫ i.left)
      (gysinBaseChangeImmersion_comm square i h hfac))
    (gysinBaseChangeImmersion_over square i h hfac)

/-- `gysinBaseChangeImmersion` is the over-morphism associated to the canonical
`pullback.lift` comparison. -/
theorem gysinBaseChangeImmersion_eq
    {S : Scheme.{u}} {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f) :
    gysinBaseChangeImmersion square i h hfac =
      Over.homMk
        (pullback.lift f'.left (g'.left ≫ i.left)
          (gysinBaseChangeImmersion_comm square i h hfac))
        (gysinBaseChangeImmersion_over square i h hfac) := sorry

/-- The base-changed maps `i'` and `h'` recover `f'`. -/
theorem gysinBaseChange_fac
    {S : Scheme.{u}} {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f) :
    gysinBaseChangeImmersion square i h hfac ≫ OpenRestriction.baseChangeToTarget h g =
      f' := sorry

/-- The square relating `i` to its base change `i'` is cartesian. -/
theorem gysinBaseChangeImmersion_isPullback
    {S : Scheme.{u}} {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f) :
    IsPullback g'.left (gysinBaseChangeImmersion square i h hfac).left i.left
      (OpenRestriction.baseChangeToSource h g).left := sorry

/-- Base change of an immersion along a cartesian square remains an immersion. -/
instance gysinBaseChangeImmersion_isImmersion
    {S : Scheme.{u}} {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f)
    [IsImmersion i.left] :
    IsImmersion (gysinBaseChangeImmersion square i h hfac).left := sorry

/-- Base change of a closed immersion along a cartesian square remains a closed immersion. -/
instance gysinBaseChangeImmersion_isClosedImmersion
    {S : Scheme.{u}} {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f)
    [IsClosedImmersion i.left] :
    IsClosedImmersion (gysinBaseChangeImmersion square i h hfac).left := sorry

/-- The induced immersion in a smooth factorization of the primed lci morphism is
regular over a locally Noetherian target. This uses primed lci, not preservation of
regular immersions under arbitrary base change. -/
instance gysinBaseChangeImmersion_isRegularImmersion
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y X' Y' P : Over S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (square : IsPullback g'.left f'.left f.left g.left)
    (i : X ⟶ P) (h : P ⟶ Y) (hfac : i ≫ h = f)
    [IsRegularImmersion i.left] [LocallyOfFiniteType Y'.hom]
    [Smooth h.left] [LocallyOfType RingHom.IsLocalCompleteIntersection f'.left] :
    IsRegularImmersion (gysinBaseChangeImmersion square i h hfac).left := sorry

/-- Base change of a smooth morphism remains smooth. -/
instance gysinBaseChangeToTarget_smooth
    {S : Scheme.{u}} {P Y Y' : Over S} (h : P ⟶ Y) (g : Y' ⟶ Y)
    [Smooth h.left] : Smooth (OpenRestriction.baseChangeToTarget h g).left := sorry

/-- Base change preserves relative dimension of a smooth factor. -/
instance gysinBaseChangeToTarget_relativeDimension
    {S : Scheme.{u}} {P Y Y' : Over S} (h : P ⟶ Y) (g : Y' ⟶ Y)
    (t : ℕ) [Scheme.Hom.RelativeDimension h.left t] :
    Scheme.Hom.RelativeDimension (OpenRestriction.baseChangeToTarget h g).left t := sorry

end AlgebraicGeometry.BivariantClass
