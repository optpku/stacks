module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Category

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Germ.Hom

/-- A chosen comparison of two germ morphisms after base changes satisfying `Q`.
The two cartesian presentations have a common base, and their total germs are
isomorphic over that base. -/
structure BaseLocalIso (Q : MorphismProperty Germ.{u}) {X S X' S' : Germ.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') where
  /-- The common germ over which the two presentations are compared. -/
  base : Germ.{u}
  /-- The total germ of the left cartesian presentation. -/
  left : Germ.{u}
  /-- The total germ of the right cartesian presentation. -/
  right : Germ.{u}
  /-- The map from the left total germ to the source of `f`. -/
  leftToSource : left ⟶ X
  /-- The structure map from the left total germ to the common base. -/
  leftToBase : left ⟶ base
  /-- The left base-change map. -/
  leftBase : base ⟶ S
  /-- The left presentation is cartesian. -/
  leftIsPullback : IsPullback leftToSource leftToBase f leftBase
  /-- The left base-change map satisfies `Q`. -/
  leftBaseProperty : Q leftBase
  /-- The map from the right total germ to the source of `f'`. -/
  rightToSource : right ⟶ X'
  /-- The structure map from the right total germ to the common base. -/
  rightToBase : right ⟶ base
  /-- The right base-change map. -/
  rightBase : base ⟶ S'
  /-- The right presentation is cartesian. -/
  rightIsPullback : IsPullback rightToSource rightToBase f' rightBase
  /-- The right base-change map satisfies `Q`. -/
  rightBaseProperty : Q rightBase
  /-- The comparison isomorphism over the common base. -/
  comparison : Over.mk leftToBase ≅ Over.mk rightToBase

namespace BaseLocalIso

/-- Reverse a chosen local-on-the-base comparison. -/
def symm {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') :
    BaseLocalIso Q f' f where
  base := e.base
  left := e.right
  right := e.left
  leftToSource := e.rightToSource
  leftToBase := e.rightToBase
  leftBase := e.rightBase
  leftIsPullback := e.rightIsPullback
  leftBaseProperty := e.rightBaseProperty
  rightToSource := e.leftToSource
  rightToBase := e.leftToBase
  rightBase := e.leftBase
  rightIsPullback := e.leftIsPullback
  rightBaseProperty := e.leftBaseProperty
  comparison := e.comparison.symm

/-- The defining cartesian-square and base-property conditions of a chosen comparison. -/
theorem spec {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (e : BaseLocalIso Q f f') :
    Q e.leftBase ∧ Q e.rightBase ∧
      IsPullback e.leftToSource e.leftToBase f e.leftBase ∧
      IsPullback e.rightToSource e.rightToBase f' e.rightBase := sorry

end BaseLocalIso

/-- Two germ morphisms are locally on the base isomorphic with respect to `Q` when a
chosen comparison exists. -/
def IsLocallyOnBaseIsomorphic (Q : MorphismProperty Germ.{u})
    {X S X' S' : Germ.{u}} (f : X ⟶ S) (f' : X' ⟶ S') : Prop :=
  Nonempty (BaseLocalIso Q f f')

/-- A chosen local-on-the-base comparison yields local isomorphism on the base. -/
theorem BaseLocalIso.isLocallyOnBaseIsomorphic {Q : MorphismProperty Germ.{u}}
    {X S X' S' : Germ.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    (e : BaseLocalIso Q f f') : IsLocallyOnBaseIsomorphic Q f f' :=
  ⟨e⟩

namespace IsLocallyOnBaseIsomorphic

/-- Local isomorphism on the base provides a comparison with its defining cartesian and
base-property conditions. -/
theorem exists_spec {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (h : IsLocallyOnBaseIsomorphic Q f f') :
    ∃ e : BaseLocalIso Q f f',
      Q e.leftBase ∧ Q e.rightBase ∧
        IsPullback e.leftToSource e.leftToBase f e.leftBase ∧
        IsPullback e.rightToSource e.rightToBase f' e.rightBase := by
  rcases h with ⟨e⟩
  exact ⟨e, e.spec⟩

/-- Local isomorphism on the base is symmetric. -/
theorem symm {Q : MorphismProperty Germ.{u}} {X S X' S' : Germ.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} (h : IsLocallyOnBaseIsomorphic Q f f') :
    IsLocallyOnBaseIsomorphic Q f' f := sorry

end IsLocallyOnBaseIsomorphic

end AlgebraicGeometry.Scheme.Germ.Hom
