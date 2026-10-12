/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Construction.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences induced by the full-subbicategory two-fibre-product pseudofunctor

The apex-facing specialization of the generic pseudofunctor action on bicategorical
equivalences.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]

/-- A bicategorical equivalence of bundled cospans induces the canonical equivalence of their
explicit two-fibre-product apices. -/
@[stacks 0040 "equivalence of full-subbicategory two-fibre-products"]
noncomputable def pseudofunctor.mapEquivalence
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (e : S ≌ T) :
    apex S.fst S.snd ≌ apex T.fst T.snd :=
  (pseudofunctor P).mapEquivalence e

/-- The forward morphism of an induced apex equivalence is the explicit two-fibre-product map
of the forward cospan transformation. -/
@[simp]
theorem pseudofunctor.mapEquivalence.hom
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).hom =
      _root_.CategoryTheory.TwoFibreProduct.map
        (Bicategory.Cospan.Hom.toCospanTransform e.hom) := sorry

/-- The inverse morphism of an induced apex equivalence is the explicit two-fibre-product map
of the inverse cospan transformation. -/
@[simp]
theorem pseudofunctor.mapEquivalence.inv
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).inv =
      _root_.CategoryTheory.TwoFibreProduct.map
        (Bicategory.Cospan.Hom.toCospanTransform e.inv) := sorry

/-- The unit of an induced apex equivalence is the canonical pseudofunctor unit. -/
@[simp]
theorem pseudofunctor.mapEquivalence.unit
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso (pseudofunctor P) e := sorry

/-- The counit of an induced apex equivalence is the canonical pseudofunctor counit. -/
@[simp]
theorem pseudofunctor.mapEquivalence.counit
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).counit =
      Pseudofunctor.mapEquivalence.counitIso (pseudofunctor P) e := sorry

end TwoFibreProduct

end CategoryTheory
