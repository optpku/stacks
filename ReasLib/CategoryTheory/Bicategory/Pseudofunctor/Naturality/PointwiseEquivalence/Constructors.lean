/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Components

/-!
# Componentwise constructors for pointwise equivalences

This leaf aligns independently supplied component equivalences with a fixed
strong transformation and extracts the same data from a bicategorical
equivalence of pseudofunctors.
-/

@[expose] public section

universe wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {D : Type uD} [Bicategory.{wD, vD} D]
variable {F G : Pseudofunctor B D}

namespace PointwiseEquivalence

variable {η : F ⟶ G}

/-- Equip a strong transformation with pointwise equivalence data supplied independently at
each component.

The invertible `2`-cell family `homIso` aligns the supplied forward morphisms
with the actual components of the transformation. Inverse morphisms are
retained literally. -/
@[stacks 0040 "pointwise equivalence data from component equivalences"]
def ofComponents
    (e : ∀ a : B, F.obj a ≌ G.obj a)
    (homIso : ∀ a : B, (e a).hom ≅ η.app a) :
    PointwiseEquivalence η := fun a ↦
  (Bicategory.Equivalence.OnHom.ofEquivalence (e a)).changeHom
    (homIso a)

/-- The chosen inverse component of `ofComponents` is the supplied component inverse. -/
@[simp]
theorem ofComponents.invApp
    (e : ∀ a : B, F.obj a ≌ G.obj a)
    (homIso : ∀ a : B, (e a).hom ≅ η.app a) (a : B) :
    (ofComponents e homIso).invApp a = (e a).inv := sorry

/-- The unit stored by `ofComponents` is the explicitly aligned supplied unit. -/
@[simp]
theorem ofComponents.unit
    (e : ∀ a : B, F.obj a ≌ G.obj a)
    (homIso : ∀ a : B, (e a).hom ≅ η.app a) (a : B) :
    (ofComponents e homIso).unit a =
      Bicategory.Equivalence.OnHom.changeHom.unitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence (e a))
        (homIso a) := sorry

/-- The counit stored by `ofComponents` is the explicitly aligned supplied counit. -/
@[simp]
theorem ofComponents.counit
    (e : ∀ a : B, F.obj a ≌ G.obj a)
    (homIso : ∀ a : B, (e a).hom ≅ η.app a) (a : B) :
    (ofComponents e homIso).counit a =
      Bicategory.Equivalence.OnHom.changeHom.counitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence (e a))
        (homIso a) := sorry

/-- The evaluated unit and counit of a functor-bicategory equivalence satisfy
the pointwise left triangle identity. -/
theorem ofEquivalence.left_triangle (e : F ≌ G) (a : B) :
    Bicategory.leftZigzagIso
        (StrongTrans.isoApp e.unit a)
        (StrongTrans.isoApp e.counit a) =
      λ_ (e.hom.app a) ≪≫ (ρ_ (e.hom.app a)).symm := sorry

/-- A functor-bicategory equivalence supplies pointwise equivalence data on its forward
strong transformation.

The inverse, unit, and counit are read directly from the global equivalence;
no equality transport is used to construct this data. -/
@[stacks 0040 "pointwise equivalence data of a pseudofunctor equivalence"]
def ofEquivalence (e : F ≌ G) :
    PointwiseEquivalence e.hom := fun a ↦
  { inv := e.inv.app a
    unit := StrongTrans.isoApp e.unit a
    counit := StrongTrans.isoApp e.counit a
    left_triangle := ofEquivalence.left_triangle e a }

/-- The chosen inverse in the pointwise equivalence extracted from a global equivalence is
the corresponding component of its inverse strong transformation. -/
@[simp]
theorem ofEquivalence.invApp (e : F ≌ G) (a : B) :
    (ofEquivalence e).invApp a =
      e.inv.app a := sorry

/-- The component equivalence extracted from a global equivalence is its strict pointwise
evaluation. -/
@[simp]
theorem ofEquivalence.app (e : F ≌ G) (a : B) :
    (ofEquivalence e).app a =
      e.app a := sorry

/- Data audit (mathlib 4.32): `ofComponents` uses the explicit invertible
`2`-cells in `homIso`, never equality elimination, to align units and counits.
`ofEquivalence` reads inverse, unit, and counit components directly from the
supplied global equivalence. Any `sorryAx` is confined to triangle fields and
readout propositions. -/

end PointwiseEquivalence

end Pseudofunctor.StrongTrans

end CategoryTheory
