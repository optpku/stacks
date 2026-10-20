/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.IsoCat
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Functor.OverIso

/-!
# Strict API for categories over a base

This module contains strict morphisms over a fixed base, heterogeneous strict isomorphisms, and
the elementary extensionality and constructor API for `BasedCategory` and `BasedFunctor`.
-/

@[expose] public section

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open BasedNatTrans
open Functor.IsHomLift

universe u v uS uX uY vS vX vY

variable {C : Type u} [Category.{v} C]

/-- A strict isomorphism between categories over the same base, allowing the two total
categories to live in different universes. The inherited `IsoCat` owns the forward functor,
strict inverse, and the two inverse equations; the extra datum says that the forward functor lies
strictly over the common base. Compatibility of the inverse follows from this datum and the
strict counit equation.

Ordinary `X ≅ Y` in the category `BasedCategory C` is restricted to one fixed pair of total
category universes. This heterogeneous owner is therefore required by constructions such as
co-Grothendieck strictification, whose total category also stores arrows of the base. -/
structure BasedCategory.StrictIso (X : BasedCategory.{vX, uX} C) (Y : BasedCategory.{vY, uY} C)
    extends IsoCat X.obj Y.obj where
  /-- The forward functor commutes strictly with the projections to the base. -/
  functor_w : toIsoCat.functor ⋙ Y.p = X.p

namespace BasedCategory.StrictIso

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- An isomorphism of total categories whose forward functor commutes strictly with the
projections determines a strict isomorphism over the common base. -/
def ofIsoCat (e : IsoCat X.obj Y.obj) (h : e.functor ⋙ Y.p = X.p) :
    BasedCategory.StrictIso X Y where
  toIsoCat := e
  functor_w := h

/-- The inverse functor automatically commutes strictly with the projections. This is derived
from `functor_w` and the strict counit equation rather than stored as duplicate structure data. -/
theorem inverse_w (e : BasedCategory.StrictIso X Y) :
    e.toIsoCat.inverse ⋙ X.p = Y.p := sorry
/- Proof strategy: whisker `e.functor_w` on the left by `e.toIsoCat.inverse`, reassociate, and
rewrite `e.toIsoCat.inverse ⋙ e.toIsoCat.functor` using `e.toIsoCat.counit_eq`. -/

/-- The forward based functor of a heterogeneous strict isomorphism over the base. -/
def hom (e : BasedCategory.StrictIso X Y) : X ⥤ᵇ Y where
  toFunctor := e.toIsoCat.functor
  w := e.functor_w

/-- The inverse based functor of a heterogeneous strict isomorphism over the base. -/
def inv (e : BasedCategory.StrictIso X Y) : Y ⥤ᵇ X where
  toFunctor := e.toIsoCat.inverse
  w := e.inverse_w

end BasedCategory.StrictIso

namespace BasedCategory

/-- Two based categories over the same base are equal when their carrier types, category
structures, and projection functors agree. -/
@[ext]
theorem ext
    {X Y : BasedCategory.{vX, uX} C}
    (hobj : X.obj = Y.obj) (hcategory : HEq X.category Y.category) (hp : HEq X.p Y.p) :
    X = Y := sorry
/- Proof strategy: destruct `X` and `Y`, eliminate the carrier equality and the two
heterogeneous field equalities, and conclude by reflexivity. -/

variable {X : BasedCategory.{vX, uX} C}

/-- The projection of a based category commutes strictly with the identity projection on its
base. -/
theorem toBase_w (X : BasedCategory.{vX, uX} C) : X.p ⋙ 𝟭 C = X.p := sorry
/- Proof strategy: this is exactly `Functor.comp_id X.p`; reduce the projection of
`BasedCategory.ofFunctor (𝟭 C)` only when the theorem is used to build `toBase`. -/

/-- The canonical morphism in `Cat/C` from a category over `C` to the base object `(C, 𝟭 C)`.

This is a data owner rather than an `abbrev`: downstream statements should read through the
based-functor projections, not depend on reducibility of its structure literal. -/
def toBase (X : BasedCategory.{vX, uX} C) : X ⥤ᵇ ofFunctor (𝟭 C) where
  toFunctor := X.p
  w := toBase_w X

end BasedCategory

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- A based functor is faithful whenever the projection of its source is faithful. This is the
canonical instance obtained by applying the target projection to an equality after mapping. -/
instance faithfulOfSource (F : X ⥤ᵇ Y) [X.p.Faithful] : F.Faithful := sorry
/- Proof strategy: apply `X.p.map_injective`, rewrite the strict projection equation of `F`, and
use the assumed equality after `F.map`. -/

/-- Two based functors are equal when their underlying functors are equal; their strict
base-commutativity fields are proof-valued. -/
@[ext]
theorem ext {F G : X ⥤ᵇ Y} (h : F.toFunctor = G.toFunctor) : F = G := sorry
/- Proof strategy: destruct `F` and `G`; the underlying-functor equality identifies their data
fields, and proof irrelevance identifies the strict base-commutativity fields. -/

/-- Composing a based functor with the projection of its target gives the projection of its
source. -/
theorem comp_toBase (φ : X ⥤ᵇ Y) :
    φ ⋙ BasedCategory.toBase Y = BasedCategory.toBase X := sorry

/-- Bundle a functor between the total categories together with a strict commutativity equation
over `C`. This is the unbundled-input constructor complementary to `BasedCategory.ofFunctor`. -/
def ofFunctor
    {S : Type uX} [Category.{vX} S] {T : Type uY} [Category.{vY} T]
    {p : S ⥤ C} {q : T ⥤ C} (F : S ⥤ T) (w : F ⋙ q = p) :
    BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q where
  toFunctor := F
  w := w

/-- The canonical natural isomorphism expressing the strict projection equation of a based
functor. This is the comparison to use when a construction is formulated for triangles
commuting up to isomorphism; its only input is the based functor's stored strict equation. -/
def projectionIso (F : X ⥤ᵇ Y) :
    F.toFunctor ⋙ Y.p ≅ X.p :=
  eqToIso F.w

/-- Regard a based functor as a pseudo-slice morphism. The comparison is the canonical
isomorphism attached to its stored strict projection equation. -/
def toOverIso (F : X ⥤ᵇ Y) : Functor.OverIso X.p Y.p where
  functor := F.toFunctor
  iso := F.projectionIso

end BasedFunctor

end CategoryTheory
