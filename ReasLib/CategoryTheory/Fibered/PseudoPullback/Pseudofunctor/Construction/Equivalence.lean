module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Construction.Action
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Pseudofunctor.Mapping
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences induced by the explicit pseudo-pullback pseudofunctor

The equivalence of explicit pseudo-pullbacks induced by an equivalence of bundled cospans,
together with direct readouts of its structure maps.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped Bicategory

universe u v w vB

namespace CategoryTheory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

/-- A bicategorical equivalence of bundled based cospans induces the canonical equivalence of
their explicit pseudo-pullback apices.

This apex-facing specialization of `Pseudofunctor.mapEquivalence` is the convenient owner for
applications that work directly with explicit pseudo-pullbacks rather than the bundled-cospan
pseudofunctor. -/
@[stacks 0040 "equivalence of explicit pseudo-pullbacks induced by a cospan equivalence"]
noncomputable def pseudofunctor.mapEquivalence
    {S T : Bicategory.Cospan
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (e : S ≌ T) :
    PseudoPullback S.fst S.snd ≌ PseudoPullback T.fst T.snd :=
  (pseudofunctor C).mapEquivalence e

/-- The forward morphism of the equivalence induced by a bundled cospan equivalence is the
explicit pseudo-pullback map of its forward cospan transformation. -/
@[simp]
theorem pseudofunctor.mapEquivalence.hom
    {S T : Bicategory.Cospan
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).hom =
      _root_.CategoryTheory.BasedCategory.PseudoPullback.map
        (Bicategory.Cospan.Hom.toBasedTransform e.hom) := sorry

/-- The inverse morphism of the equivalence induced by a bundled cospan equivalence is the
explicit pseudo-pullback map of its inverse cospan transformation. -/
@[simp]
theorem pseudofunctor.mapEquivalence.inv
    {S T : Bicategory.Cospan
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).inv =
      _root_.CategoryTheory.BasedCategory.PseudoPullback.map
        (Bicategory.Cospan.Hom.toBasedTransform e.inv) := sorry

/-- The unit of the pseudo-pullback equivalence induced by a cospan equivalence is the
canonical unit supplied by the bundled-cospan pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapEquivalence.unit
    {S T : Bicategory.Cospan
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).unit =
      Pseudofunctor.mapEquivalence.unitIso (pseudofunctor C) e := sorry

/-- The counit of the pseudo-pullback equivalence induced by a cospan equivalence is the
canonical counit supplied by the bundled-cospan pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapEquivalence.counit
    {S T : Bicategory.Cospan
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
    (e : S ≌ T) :
    (pseudofunctor.mapEquivalence e).counit =
      Pseudofunctor.mapEquivalence.counitIso (pseudofunctor C) e := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
