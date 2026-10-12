/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- A pullback square of schemes whose four vertices are quasi-compact and
quasi-separated. -/
structure IsQcqsPullbackSquare {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) : Prop where
  /-- The square is cartesian. -/
  isPullback : IsPullback g' f' f g
  /-- The upper-left scheme is quasi-compact. -/
  compactSpaceX' : CompactSpace X'
  /-- The upper-left scheme is quasi-separated. -/
  quasiSeparatedSpaceX' : QuasiSeparatedSpace X'
  /-- The upper-right scheme is quasi-compact. -/
  compactSpaceX : CompactSpace X
  /-- The upper-right scheme is quasi-separated. -/
  quasiSeparatedSpaceX : QuasiSeparatedSpace X
  /-- The lower-left scheme is quasi-compact. -/
  compactSpaceY' : CompactSpace Y'
  /-- The lower-left scheme is quasi-separated. -/
  quasiSeparatedSpaceY' : QuasiSeparatedSpace Y'
  /-- The lower-right scheme is quasi-compact. -/
  compactSpaceY : CompactSpace Y
  /-- The lower-right scheme is quasi-separated. -/
  quasiSeparatedSpaceY : QuasiSeparatedSpace Y

/-- A pullback square whose vertices carry the canonical quasi-compact and
quasi-separated instances is a qcqs pullback square. -/
def IsQcqsPullbackSquare.ofIsPullback {X' X Y' Y : Scheme.{u}}
    [hCompactX' : CompactSpace X'] [hQuasiSeparatedX' : QuasiSeparatedSpace X']
    [hCompactX : CompactSpace X] [hQuasiSeparatedX : QuasiSeparatedSpace X]
    [hCompactY' : CompactSpace Y'] [hQuasiSeparatedY' : QuasiSeparatedSpace Y']
    [hCompactY : CompactSpace Y] [hQuasiSeparatedY : QuasiSeparatedSpace Y]
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h : IsPullback g' f' f g) : IsQcqsPullbackSquare g' f' f g where
  isPullback := h
  compactSpaceX' := hCompactX'
  quasiSeparatedSpaceX' := hQuasiSeparatedX'
  compactSpaceX := hCompactX
  quasiSeparatedSpaceX := hQuasiSeparatedX
  compactSpaceY' := hCompactY'
  quasiSeparatedSpaceY' := hQuasiSeparatedY'
  compactSpaceY := hCompactY
  quasiSeparatedSpaceY := hQuasiSeparatedY

/-- A square of schemes is a qcqs pullback square exactly when it is cartesian
and each of its four vertices is quasi-compact and quasi-separated. -/
theorem isQcqsPullbackSquare_iff {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) :
    IsQcqsPullbackSquare g' f' f g ↔
      IsPullback g' f' f g ∧
      CompactSpace X' ∧ QuasiSeparatedSpace X' ∧
      CompactSpace X ∧ QuasiSeparatedSpace X ∧
      CompactSpace Y' ∧ QuasiSeparatedSpace Y' ∧
      CompactSpace Y ∧ QuasiSeparatedSpace Y := sorry

end AlgebraicGeometry
