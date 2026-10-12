/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import stacks_project.Chap61.Definition_61_2_3_WLocal
public import stacks_project.Chap61.«61_5_2_6_Scheme»

/-!
# Geometry of the affine w-local hull

The structure morphism `X_w ⟶ Spec(A)`, the induced point-set bijection
`Z → Spec(A)`, and the identification of `Z` with the closed points of `X_w`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open Algebra.WLocalHull

noncomputable section

universe u

namespace AlgebraicGeometry.WLocal.Construction

variable (A : Type u) [CommRing A]

/-- The structure morphism `X_w ⟶ Spec(A)` through the empty-stage projection. -/
def toSpec : scheme A ⟶ Spec (.of A) :=
  scheme_π A ∅ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (stage A ∅)))

/-- `toSpec` is the composite of the empty-stage projection with `Spec` of
`A → A_∅`. -/
theorem toSpec_eq :
    toSpec A = scheme_π A ∅ ≫ Spec.map (CommRingCat.ofHom (algebraMap A (stage A ∅))) :=
  sorry

/-- The induced morphism `Z ⟶ Spec(A)` of the closed subscheme of `X_w`. -/
def closedToSpec : closedSubscheme A ⟶ Spec (.of A) :=
  closedι A ≫ toSpec A

/-- `closedToSpec` is the composite of the closed immersion `Z ⟶ X_w` with
`toSpec`. -/
theorem closedToSpec_eq : closedToSpec A = closedι A ≫ toSpec A :=
  sorry

/-- The morphism `X_w ⟶ Spec(A)` induces a bijection on points `Z → Spec(A)`. -/
theorem bijective_closedToSpec : Function.Bijective (closedToSpec A) :=
  sorry

/-- The image of `Z ⟶ X_w` is the set of closed points of `X_w`. -/
theorem range_closedι_eq_closedPoints :
    Set.range (closedι A) = closedPoints (scheme A) :=
  sorry

/-- The closed subscheme `Z ⊂ X_w` is reduced. -/
instance instIsReduced_closedSubscheme : IsReduced (closedSubscheme A) :=
  sorry

/-- Every point of `X_w` specializes to a unique point of `Z`. -/
theorem existsUnique_specializes_mem_range_closedι (x : scheme A) :
    ∃! y, y ∈ Set.range (closedι A) ∧ x ⤳ y :=
  sorry

/-- The affine hull `X_w` is a w-local space. -/
instance instWLocalSpace : WLocalSpace (scheme A) :=
  sorry

end AlgebraicGeometry.WLocal.Construction
