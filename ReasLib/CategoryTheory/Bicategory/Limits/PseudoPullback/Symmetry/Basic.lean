module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

/-!
# Symmetry of readable pseudopullback-cone data

Reversing the two legs of a cospan reverses a readable pseudopullback cone without changing
its apex. This leaf contains only the presentation-level operation and its field computations;
transport of the bilimit property is layered separately.

No morphism of cone bicategories is needed for this data operation: `swap` acts directly on
the four concrete fields of `PseudoPullbackCone`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Reverse the two legs of a readable pseudopullback cone. The apex is unchanged, the two
projections are exchanged, and the comparison isomorphism is inverted. -/
def swap (P : PseudoPullbackCone f g) : PseudoPullbackCone g f where
  pt := P.pt
  fst := P.snd
  snd := P.fst
  iso := P.iso.symm

/-- Swapping a readable pseudopullback cone leaves its apex unchanged. -/
@[simp]
theorem swap.pt (P : PseudoPullbackCone f g) :
    P.swap.pt = P.pt := sorry

/-- The first projection of a swapped cone is the original second projection. -/
@[simp]
theorem swap.fst (P : PseudoPullbackCone f g) :
    P.swap.fst = P.snd := sorry

/-- The second projection of a swapped cone is the original first projection. -/
@[simp]
theorem swap.snd (P : PseudoPullbackCone f g) :
    P.swap.snd = P.fst := sorry

/-- The comparison isomorphism of a swapped cone is the inverse original comparison. -/
@[simp]
theorem swap.iso (P : PseudoPullbackCone f g) :
    P.swap.iso = P.iso.symm := sorry

/-- The forward comparison cell of a swapped cone is the inverse original comparison cell. -/
@[simp]
theorem swap.iso.hom (P : PseudoPullbackCone f g) :
    P.swap.iso.hom = P.iso.inv := sorry

/-- The inverse comparison cell of a swapped cone is the forward original comparison cell. -/
@[simp]
theorem swap.iso.inv (P : PseudoPullbackCone f g) :
    P.swap.iso.inv = P.iso.hom := sorry

/-- Reversing the legs of a readable pseudopullback cone twice recovers the original cone. -/
@[simp]
theorem swap.involution (P : PseudoPullbackCone f g) :
    P.swap.swap = P := sorry

/- Data and axiom audit (mathlib 4.32): `swap` copies the apex and projections directly and
applies `Iso.symm` to the stored comparison. Its non-`Prop` data therefore introduces no choice
and no `sorryAx`; all deferred content is confined to equality statements. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
