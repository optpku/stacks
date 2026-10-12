/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Family.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Pseudofunctor.Mapping
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Selected bilimit apexes of equivalent diagrams

An equivalence between diagrams is sent by the selected-apex pseudofunctor to an
equivalence between their selected bilimit apexes. This file provides a family-facing name
for that equivalence and exposes its four principal fields.

The final theorem transports any equivalence-closed object property between the selected
apexes; no limit-specific reconstruction of the property is required.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]

namespace BilimitConeFamily

/-- The equivalence between selected bilimit apexes induced by an equivalence of
diagrams. -/
noncomputable abbrev apexEquivalence
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (e : E ≌ F) :
    L.apex E ≌ L.apex F :=
  L.apexPseudofunctor.mapEquivalence e

/-- The forward morphism of the induced apex equivalence is the selected universal map
along the forward diagram transformation. -/
@[simp]
theorem apexEquivalence.hom
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (e : E ≌ F) :
    (L.apexEquivalence e).hom = L.map e.hom := sorry

/-- The inverse morphism of the induced apex equivalence is the selected universal map
along the inverse diagram transformation. -/
@[simp]
theorem apexEquivalence.inv
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (e : E ≌ F) :
    (L.apexEquivalence e).inv = L.map e.inv := sorry

/-- The unit of the induced apex equivalence is the canonical unit obtained by mapping the
diagram equivalence through the selected-apex pseudofunctor. -/
@[simp]
theorem apexEquivalence.unit
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (e : E ≌ F) :
    (L.apexEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso L.apexPseudofunctor e := sorry

/-- The counit of the induced apex equivalence is the canonical counit obtained by mapping
the diagram equivalence through the selected-apex pseudofunctor. -/
@[simp]
theorem apexEquivalence.counit
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (e : E ≌ F) :
    (L.apexEquivalence e).counit =
      Pseudofunctor.mapEquivalence.counitIso L.apexPseudofunctor e := sorry

/-- An equivalence-closed object property has the same truth value on the selected bilimit
apexes of equivalent diagrams. -/
theorem apexEquivalence.objectProperty_iff
    (L : BilimitConeFamily (J := J) (B := B))
    (P : ObjectProperty B) [P.IsClosedUnderEquivalences]
    {E F : Pseudofunctor J B} (e : E ≌ F) :
    P (L.apex E) ↔ P (L.apex F) := sorry

/- Data and axiom audit (mathlib 4.32):

`apexEquivalence` is exactly the image of the explicit diagram equivalence under
`apexPseudofunctor`. Its maps and coherence cells are therefore inherited from the
pseudofunctor's already named data; no new inverse, unit, counit, or choice is selected. -/

end BilimitConeFamily

end Bicategory

end CategoryTheory
