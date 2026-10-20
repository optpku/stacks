/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import ReasLib.CategoryTheory.Subobject.Quotient.Map

/-!
# Intersection Quotients of Subobjects

This leaf module provides the quotient `Y / (X ⊓ Y)` of two subobjects of a common ambient
object.  It is independent of the heavier exactness and subquotient infrastructure, so it can be
used directly by constructions such as spectral-sequence page representatives.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Subobject

variable [HasZeroMorphisms C] [HasCokernels C] [HasPullbacks C]

/-- The quotient of a subobject `Y` by its intersection with a second subobject `X`.

This construction is defined for arbitrary `X` and `Y`; when `X ≤ Y`, it is isomorphic to the
usual quotient `Y / X`. It is represented directly as a cokernel, so its quotient projection is
available without choosing an embedded subquotient representative. -/
@[stacks 012M "intersection quotient of subobjects"]
noncomputable def intersectionQuotient {A : C} (X Y : Subobject A) : C :=
  cokernel (Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right)

namespace IntersectionQuotient

/-- The canonical projection from `Y` to the intersection quotient `Y / (X ⊓ Y)`. -/
@[stacks 012M "intersection quotient projection"]
noncomputable abbrev π {A : C} (X Y : Subobject A) :
    (Y : C) ⟶ intersectionQuotient X Y :=
  cokernel.π (Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right)

/-- The canonical projection to an intersection quotient is an epimorphism. -/
@[stacks 012M "intersection quotient projection is epi"]
instance epi_π {A : C} (X Y : Subobject A) :
    Epi (π X Y) := sorry

/-- Descend a morphism from `Y` through the quotient `Y / (X ⊓ Y)`. -/
@[stacks 012M "intersection quotient desc"]
noncomputable def desc {A T : C} (X Y : Subobject A) (f : (Y : C) ⟶ T)
    (hf : Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right ≫ f = 0) :
    intersectionQuotient X Y ⟶ T :=
  cokernel.desc _ f hf

/-- Composing the intersection-quotient projection with a descended map recovers the original
morphism. -/
@[simp, stacks 012M "intersection quotient projection desc"]
theorem π_desc {A T : C} (X Y : Subobject A) (f : (Y : C) ⟶ T)
    (hf : Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right ≫ f = 0) :
    π X Y ≫ desc X Y f hf = f := sorry

/-- Morphisms out of an intersection quotient are determined by their composites with the
canonical quotient projection. -/
@[ext, stacks 012M "intersection quotient morphism extensionality"]
theorem hom_ext {A T : C} (X Y : Subobject A)
    {f g : intersectionQuotient X Y ⟶ T}
    (h : π X Y ≫ f = π X Y ≫ g) : f = g := sorry

/-- A commutative square between the defining inclusions induces a map of intersection
quotients. The subobjects are inferred from the two vertical arrows. -/
@[stacks 012M "intersection quotient map"]
noncomputable abbrev map {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    (p : ((X ⊓ Y : Subobject A) : C) ⟶ ((X' ⊓ Y' : Subobject B) : C))
    (q : (Y : C) ⟶ (Y' : C))
    (hpq : Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right ≫ q =
      p ≫ Subobject.ofLE (X' ⊓ Y') Y' _root_.inf_le_right) :
    intersectionQuotient X Y ⟶ intersectionQuotient X' Y' :=
  Subobject.Quotient.map p q hpq

/-- The map of intersection quotients is characterized by the naturality of their quotient
projections. -/
@[reassoc (attr := simp), stacks 012M "intersection quotient projection map"]
theorem π_map {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    (p : ((X ⊓ Y : Subobject A) : C) ⟶ ((X' ⊓ Y' : Subobject B) : C))
    (q : (Y : C) ⟶ (Y' : C))
    (hpq : Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right ≫ q =
      p ≫ Subobject.ofLE (X' ⊓ Y') Y' _root_.inf_le_right) :
    π X Y ≫ map p q hpq = q ≫ π X' Y' := sorry

/-- A morphism between intersection quotients is induced by a map between their ambient
numerator representatives when it commutes with the canonical quotient projections. -/
@[stacks 012M "intersection quotient induced map"]
abbrev IsInduced {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    (q : (Y : C) ⟶ (Y' : C))
    (f : intersectionQuotient X Y ⟶ intersectionQuotient X' Y') : Prop :=
  Subobject.Quotient.IsInduced
    (hXY := _root_.inf_le_right) (hX'Y' := _root_.inf_le_right) q f

/-- The canonical map of intersection quotients is induced by its supplied map between numerator
representatives. -/
@[stacks 012M "canonical intersection quotient map is induced"]
theorem map_isInduced {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    (p : ((X ⊓ Y : Subobject A) : C) ⟶ ((X' ⊓ Y' : Subobject B) : C))
    (q : (Y : C) ⟶ (Y' : C))
    (hpq : Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right ≫ q =
      p ≫ Subobject.ofLE (X' ⊓ Y') Y' _root_.inf_le_right) :
    IsInduced q (map p q hpq) := sorry

/-- An ambient morphism preserving the numerator and boundary-cycle intersection admits an
induced map of intersection quotients.  This existence statement does not choose a quotient map
from the factorization witnesses; use `map` when the restricted maps and square are explicit. -/
@[stacks 012M "existence of an ambient intersection quotient map"]
theorem existsMap {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    (f : A ⟶ B)
    (h_numerator : Y'.Factors (Y.arrow ≫ f))
    (h_intersection : (X' ⊓ Y').Factors ((X ⊓ Y).arrow ≫ f)) :
    ∃ g : intersectionQuotient X Y ⟶ intersectionQuotient X' Y',
      IsInduced (Y'.factorThru (Y.arrow ≫ f) h_numerator) g := sorry

/-- An ambient morphism preserving the numerator and boundary-cycle intersection induces a
unique map of intersection quotients once its numerator restriction is fixed. -/
@[stacks 012M "unique ambient intersection quotient map"]
theorem existsUniqueMap {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    (f : A ⟶ B)
    (h_numerator : Y'.Factors (Y.arrow ≫ f))
    (h_intersection : (X' ⊓ Y').Factors ((X ⊓ Y).arrow ≫ f)) :
    ∃! g : intersectionQuotient X Y ⟶ intersectionQuotient X' Y',
      IsInduced (Y'.factorThru (Y.arrow ≫ f) h_numerator) g := sorry

/-- If `X ≤ Y`, the intersection quotient `Y / (X ⊓ Y)` is isomorphic to the ordinary quotient
`Y / X`. -/
@[stacks 012M "intersection quotient comparison"]
theorem isIsomorphicOfLE {A : C} (X Y : Subobject A) (hXY : X ≤ Y) :
    IsIsomorphic (intersectionQuotient X Y) (cokernel (Subobject.ofLE X Y hXY)) := sorry

end IntersectionQuotient

end Subobject

end CategoryTheory
