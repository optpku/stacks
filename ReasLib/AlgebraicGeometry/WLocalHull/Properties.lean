module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.Algebra.WLocalHull.Properties
public import ReasLib.AlgebraicGeometry.WLocalHull.Limit

/-!
# Geometry of the affine w-local hull

The canonical affine w-local hull has a reduced closed subscheme whose points
map bijectively to the original spectrum. Its image is the set of closed points,
and every hull point specializes uniquely to a point of that image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open Algebra.WLocalHull

noncomputable section

universe u

namespace AlgebraicGeometry.WLocal.Construction

variable (A : Type u) [CommRing A]

/-- The structure morphism from the affine w-local hull to the original spectrum,
through the empty-stage projection. -/
def toSpec : scheme A ⟶ Spec (.of A) :=
  scheme_π A ∅ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (stage A ∅)))

/-- The hull's structure morphism is the empty-stage projection followed by
the spectrum of the empty-stage algebra map. -/
theorem toSpec_eq :
    toSpec A = scheme_π A ∅ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (stage A ∅))) :=
  rfl

/-- The structure morphism from the canonical closed subscheme of the affine
w-local hull to the original spectrum. -/
def closedToSpec : closedSubscheme A ⟶ Spec (.of A) :=
  closedι A ≫ toSpec A

/-- The closed subscheme's structure morphism is its inclusion followed by
the hull's structure morphism. -/
theorem closedToSpec_eq : closedToSpec A = closedι A ≫ toSpec A :=
  rfl

/-- The canonical closed subscheme of the affine w-local hull maps bijectively
on points to the original spectrum. -/
theorem bijective_closedToSpec : Function.Bijective (closedToSpec A) :=
  sorry

/-- The image of the canonical closed subscheme is the set of closed points
of the affine w-local hull. -/
theorem range_closedι_eq_closedPoints :
    Set.range (closedι A) = closedPoints (scheme A) :=
  sorry

/-- The canonical closed subscheme of the affine w-local hull is reduced. -/
instance instIsReduced_closedSubscheme : IsReduced (closedSubscheme A) :=
  sorry

/-- Every point of the affine w-local hull specializes to a unique point in
the image of its canonical closed subscheme. -/
theorem existsUnique_specializes_mem_range_closedι (x : scheme A) :
    ∃! y, y ∈ Set.range (closedι A) ∧ x ⤳ y :=
  sorry

/-- The carrier of the canonical affine w-local hull is a w-local space. -/
instance instWLocalSpace : WLocalSpace (scheme A) :=
  Algebra.WLocalHull.instWLocalSpace A

end AlgebraicGeometry.WLocal.Construction
