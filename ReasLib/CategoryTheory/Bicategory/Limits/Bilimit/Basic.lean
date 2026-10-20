module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Basic
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Constant.Diagram

/-!
# Conical bilimits in a bicategory

A conical pseudocone is modeled by the colax costructured-arrow bicategory of the
constant-diagram pseudofunctor. Its bilimit property is the shape-independent Yoneda
condition that every represented comparison functor is an equivalence of categories.

`BilimitCone`, `HasBilimit`, and `HasBilimitsOfShape` parallel mathlib's
`Limits.LimitCone`, `Limits.HasLimit`, and `Limits.HasLimitsOfShape`. This file contains
only the basic cone and existence layer; morphism computations, universal lifts, uniqueness,
and concrete constructions belong to downstream modules.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u wJ vJ uJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

/-- A conical pseudocone on `F`, realized by the generic colax costructured-arrow
bicategory for the constant-diagram pseudofunctor.

The adjective “pseudo” concerns the strong transformation `Pseudofunctor.const J X ⟶ F`
carried by each object. A morphism between varying-apex pseudocones carries an arbitrary
modification, not necessarily an invertible one; restricting it would incorrectly turn
the represented hom-category into a groupoid. -/
abbrev PseudoCone (F : J ⥤ᵖ B) :=
  ColaxCostructuredArrow (Pseudofunctor.constDiagram J B) F

namespace PseudoCone

variable {F : J ⥤ᵖ B}

/-- Construct a pseudocone from its apex and its strong transformation to `F`. -/
def mk (pt : B) (π : Pseudofunctor.const J pt ⟶ F) : PseudoCone F :=
  ColaxCostructuredArrow.mk pt π

/-- The apex of a pseudocone. -/
abbrev pt (s : PseudoCone F) : B :=
  s.left

/-- The strong transformation from the constant diagram at the apex to `F`. -/
abbrev π (s : PseudoCone F) : Pseudofunctor.const J s.pt ⟶ F :=
  s.hom

/-- The apex of a pseudocone constructed from explicit data is the supplied apex. -/
@[simp]
theorem mk_pt (pt : B) (hπ : Pseudofunctor.const J pt ⟶ F) :
    (mk pt hπ).pt = pt := sorry

/-- The cone transformation of a pseudocone constructed from explicit data is the supplied
transformation. -/
@[simp]
theorem mk_π (pt : B) (hπ : Pseudofunctor.const J pt ⟶ F) :
    (mk pt hπ).π = hπ := sorry

/-- A pseudocone is a bilimit cone when every represented comparison functor is an
equivalence of categories.

This is the bicategorical Yoneda representability condition and retains both `1`- and
`2`-dimensional uniqueness data. The predicate is stated on the unresized comparison
functors: equivalence is invariant under universe resizing, while the direct form exposes
the API used by universal-property arguments. -/
@[stacks 003Q "canonical represented generalization of a 2-fibre-product square"]
abbrev IsBilimit (s : PseudoCone F) : Prop :=
  ColaxCostructuredArrow.IsUniversal s

end PseudoCone

/-- A `BilimitCone F` is an explicitly selected conical pseudocone together with its
bilimit universal property.

This is the bicategorical analogue of mathlib's `Limits.LimitCone F`. It is the data owner
to retain when a particular cone matters computationally; `HasBilimit F` records only
existence. -/
structure BilimitCone (F : J ⥤ᵖ B) where
  /-- The explicitly selected conical pseudocone. -/
  cone : PseudoCone F
  /-- The selected pseudocone satisfies the bilimit universal property. -/
  isBilimit : cone.IsBilimit

namespace BilimitCone

variable {F : J ⥤ᵖ B}

/-- The cone stored by a `BilimitCone` carries its specified bilimit instance. -/
def coneIsBilimit (d : BilimitCone F) : d.cone.IsBilimit :=
  d.isBilimit

/-- Bundle a pseudocone whose bilimit property is already available as an instance. -/
def ofIsBilimit (S : PseudoCone F) [S.IsBilimit] : BilimitCone F where
  cone := S
  isBilimit := inferInstance

/-- The cone underlying `ofIsBilimit` is the supplied pseudocone. -/
@[simp]
theorem ofIsBilimit_cone (S : PseudoCone F) [S.IsBilimit] :
    (ofIsBilimit S).cone = S := sorry

end BilimitCone

/-- `HasBilimit F` asserts the existence of a bilimit cone on `F`.

Unlike `BilimitCone F`, this is deliberately propositional. The `Nonempty` wrapper is
appropriate because this declaration expresses genuine existence; computation-oriented
clients should retain an explicit `BilimitCone F`. -/
class HasBilimit (F : J ⥤ᵖ B) : Prop where mk' ::
  /-- There exists a bilimit cone on the diagram. -/
  exists_bilimit : Nonempty (BilimitCone F)

/-- An explicitly supplied bilimit cone proves existence of a bilimit. -/
theorem HasBilimit.mk {F : J ⥤ᵖ B} (d : BilimitCone F) :
    HasBilimit F := sorry

/-- A bicategory has bilimits of shape `J` when every `J`-shaped pseudodiagram admits a
bilimit cone. -/
class HasBilimitsOfShape (J : Type uJ) (B : Type u)
    [Bicategory.{wJ, vJ} J] [Bicategory.{w, v} B] : Prop where
  /-- Every pseudodiagram of the specified shape has a bilimit. -/
  has_bilimit (F : J ⥤ᵖ B) : HasBilimit F

attribute [instance] HasBilimitsOfShape.has_bilimit

/- Data and axiom audit (mathlib 4.32):

`BilimitCone` stores its pseudocone explicitly. Any `sorryAx` dependency of its constructors
is confined to the `Prop`-valued universal-property field and inherited coherence; it does
not provide the cone, apex, or cone transformation. `HasBilimit` uses `Nonempty` only for
the genuine existence proposition and exposes no choice-based extraction. -/

end Bicategory

end CategoryTheory
