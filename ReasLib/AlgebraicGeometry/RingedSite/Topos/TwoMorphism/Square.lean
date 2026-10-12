/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary

/-!
# Lax squares of morphisms of ringed topoi

This neutral leaf bundles four morphisms of ringed topoi and a forward `2`-cell between their
two composites.  Invertibility is kept as a Prop-valued companion, so users can request a
pseudo-commutative square without selecting inverse data.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w

namespace RingedSite.ToposHom

variable (A : RingedSite.{u₀, v₀, w}) (B : RingedSite.{u₁, v₁, w})
variable (C : RingedSite.{u₂, v₂, w}) (D : RingedSite.{u₃, v₃, w})
variable [A.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [B.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [C.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- A lax square of morphisms of ringed topoi.  The `2`-cell is stored in direct-image
orientation, from the upper-right composite to the left-lower composite. -/
structure LaxCommSquare where
  /-- The upper edge. -/
  upper : ToposHom A B
  /-- The left edge. -/
  left : ToposHom A C
  /-- The right edge. -/
  right : ToposHom B D
  /-- The lower edge. -/
  lower : ToposHom C D
  /-- The forward `2`-cell comparing the two composites. -/
  cell : TwoMorphism (ToposHom.comp upper right) (ToposHom.comp left lower)

/-- The composite around the upper and right sides of a lax ringed-topos square. -/
noncomputable abbrev LaxCommSquare.upperRight
    (sq : LaxCommSquare A B C D) : ToposHom A D :=
  ToposHom.comp sq.upper sq.right

/-- The composite around the left and lower sides of a lax ringed-topos square. -/
noncomputable abbrev LaxCommSquare.leftLower
    (sq : LaxCommSquare A B C D) : ToposHom A D :=
  ToposHom.comp sq.left sq.lower

/-- A lax ringed-topos square is invertible when its stored forward `2`-cell has invertible
underlying natural transformation.  This records only a proposition, not inverse data. -/
class LaxCommSquare.IsInvertible (sq : LaxCommSquare A B C D) : Prop where
  /-- The underlying natural transformation of the square cell is invertible. -/
  cell_isIso : IsIso sq.cell.hom

attribute [instance] LaxCommSquare.IsInvertible.cell_isIso

/-- Lemma 18.22.3 (04J8): a commutative square of arbitrary morphisms of ringed topoi,
carrying the chosen invertible `2`-cell as reusable data. -/
@[stacks 04J8 "commutative square"]
structure CommSquare where
  /-- The upper edge. -/
  upper : ToposHom A B
  /-- The left edge. -/
  left : ToposHom A C
  /-- The right edge. -/
  right : ToposHom B D
  /-- The lower edge. -/
  lower : ToposHom C D
  /-- The invertible `2`-cell comparing the two composites. -/
  cell : TwoIso (ToposHom.comp upper right) (ToposHom.comp left lower)

/-- The composite around the upper and right sides of a commutative ringed-topos square. -/
noncomputable abbrev CommSquare.upperRight
    (sq : CommSquare A B C D) : ToposHom A D :=
  ToposHom.comp sq.upper sq.right

/-- The composite around the left and lower sides of a commutative ringed-topos square. -/
noncomputable abbrev CommSquare.leftLower
    (sq : CommSquare A B C D) : ToposHom A D :=
  ToposHom.comp sq.left sq.lower

/-- Forget the chosen inverse of a commutative ringed-topos square. -/
def CommSquare.toLaxCommSquare (sq : CommSquare A B C D) :
    LaxCommSquare A B C D where
  upper := sq.upper
  left := sq.left
  right := sq.right
  lower := sq.lower
  cell := sq.cell.hom

end RingedSite.ToposHom
