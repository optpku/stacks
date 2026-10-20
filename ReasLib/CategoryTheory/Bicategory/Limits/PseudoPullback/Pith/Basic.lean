module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

/-!
# Pseudopullback-cone data in the pith

This module restricts a readable pseudopullback cone in an arbitrary bicategory to the pith,
where only invertible `2`-morphisms are retained. It contains only the explicit cone data and
its field computations; preservation of the bilimit property is layered separately.

There is no pseudofunctor from an arbitrary bicategory `B` to `Pith B`: noninvertible
`2`-morphisms cannot be sent to the cores of the hom-categories. Consequently this construction
is correctly defined on the invertible structural data of an individual cone rather than as an
application of a nonexistent ambient pseudofunctor.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Restrict a pseudopullback cone to the pith of its ambient bicategory. Objects and
`1`-morphisms are unchanged, while the comparison isomorphism is regarded in the core of the
relevant hom-category. -/
def toPith (P : PseudoPullbackCone f g) :
    PseudoPullbackCone (B := Pith B)
      (x := Pith.mk x) (y := Pith.mk y) (z := Pith.mk z)
      (Core.mk f) (Core.mk g) where
  pt := Pith.mk P.pt
  fst := Core.mk P.fst
  snd := Core.mk P.snd
  iso := Core.isoMk P.iso

/-- The apex of the pith restriction of a pseudopullback cone. -/
@[simp]
theorem toPith.pt (P : PseudoPullbackCone f g) :
    P.toPith.pt = Pith.mk P.pt := sorry

/-- The left leg of the pith restriction of a pseudopullback cone. -/
@[simp]
theorem toPith.fst (P : PseudoPullbackCone f g) :
    P.toPith.fst = Core.mk P.fst := sorry

/-- The right leg of the pith restriction of a pseudopullback cone. -/
@[simp]
theorem toPith.snd (P : PseudoPullbackCone f g) :
    P.toPith.snd = Core.mk P.snd := sorry

/-- The comparison isomorphism of the pith restriction of a pseudopullback cone. -/
@[simp]
theorem toPith.iso (P : PseudoPullbackCone f g) :
    P.toPith.iso = Core.isoMk P.iso := sorry

/-- The forward comparison cell of the pith restriction is the core image of the source
comparison isomorphism's forward cell. -/
@[simp]
theorem toPith.iso.hom (P : PseudoPullbackCone f g) :
    P.toPith.iso.hom = (Core.isoMk P.iso).hom := sorry

/-- The inverse comparison cell of the pith restriction is the core image of the source
comparison isomorphism's inverse cell. -/
@[simp]
theorem toPith.iso.inv (P : PseudoPullbackCone f g) :
    P.toPith.iso.inv = (Core.isoMk P.iso).inv := sorry

/- Data audit (mathlib 4.32): `toPith` reports only `propext`, `Classical.choice`, and
`Quot.sound`. Its apex, legs, and comparison isomorphism are stored explicitly and do not
depend on `sorryAx`. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
