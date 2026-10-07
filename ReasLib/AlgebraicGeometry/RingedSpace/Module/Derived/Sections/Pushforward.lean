module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square
public import ReasLib.CategoryTheory.Functor.Derived.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived sections after direct image

This leaf specializes the generic bounded-below right-derived square to sections over an open
subset.  It exposes both one-stage composition comparisons and the resulting natural isomorphism
between the two paths in the textbook derived square.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Pushforward

variable {X Y : RingedSpace.{u}}

/-- The two-stage functor obtained by deriving sections on `f ⁻¹ᵁ V` and then restriction of
scalars. -/
@[stacks 01EZ "derived sections/direct-image square source"]
abbrev source (f : X ⟶ Y) (V : Opens Y.carrier) :=
  Square.source (moduleSectionsEvaluationFunctor X (preimageOpen f V))
    (moduleSectionsRestrictionFunctor f V)

/-- The two-stage functor obtained by derived direct image followed by derived sections on `V`. -/
@[stacks 01EZ "derived sections/direct-image square target"]
abbrev target (f : X ⟶ Y) (V : Opens Y.carrier) :=
  Square.target (RingedSpace.Hom.pushforward f) (moduleSectionsEvaluationFunctor Y V)

/-- The one-stage/two-stage comparison for sections on the preimage open followed by restriction
of scalars. -/
@[stacks 01EZ "derived restricted-sections comparison"]
noncomputable abbrev sourceComparison (f : X ⟶ Y) (V : Opens Y.carrier) :=
  Functor.RightDerived.Composition.BoundedBelow.comparison
    (moduleSectionsEvaluationFunctor X (preimageOpen f V))
    (moduleSectionsRestrictionFunctor f V)

/-- Exactness of restriction of scalars makes the source composition comparison invertible. -/
@[stacks 01EZ "derived restricted-sections comparison isomorphism"]
noncomputable instance sourceComparison_isIso (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIso (sourceComparison f V) := sorry

/-- The canonical source composition isomorphism for the derived sections square. -/
@[stacks 01EZ "derived restricted-sections comparison isomorphism"]
noncomputable def sourceComparisonIso (f : X ⟶ Y) (V : Opens Y.carrier) :=
  asIso (sourceComparison f V)

/-- The one-stage/two-stage comparison for direct image followed by sections over `V`. -/
@[stacks 01EZ "derived direct-image sections comparison"]
noncomputable abbrev targetComparison (f : X ⟶ Y) (V : Opens Y.carrier) :=
  Functor.RightDerived.Composition.BoundedBelow.comparison
    (RingedSpace.Hom.pushforward f) (moduleSectionsEvaluationFunctor Y V)

/-- Pushforwards of injectives are acyclic for sections, so the target composition comparison is
canonically invertible. -/
@[stacks 01EZ "derived direct-image sections comparison isomorphism"]
noncomputable instance targetComparison_isIso (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIso (targetComparison f V) := sorry

/-- The canonical target composition isomorphism for the derived sections square. -/
@[stacks 01EZ "derived direct-image sections comparison isomorphism"]
noncomputable def targetComparisonIso (f : X ⟶ Y) (V : Opens Y.carrier) :=
  asIso (targetComparison f V)

/-- The bounded-below derived map between the two paths in the sections/direct-image square. -/
@[stacks 01EZ "derived sections and direct image"]
noncomputable def map (f : X ⟶ Y) (V : Opens Y.carrier) :
    source f V ⟶ target f V :=
  Square.mapOfIso (Module.Sections.Pushforward.comparisonIso f V).hom
    (sourceComparisonIso f V)

/-- The derived sections/direct-image map satisfies the canonical comparison equation. -/
@[stacks 01EZ "derived sections/direct-image square specification"]
abbrev IsMap (f : X ⟶ Y) (V : Opens Y.carrier)
    (η : source f V ⟶ target f V) : Prop :=
  Square.IsMapOfIso (Module.Sections.Pushforward.comparisonIso f V).hom
    (sourceComparisonIso f V) η

/-- The canonical derived sections/direct-image map satisfies its comparison specification. -/
@[stacks 01EZ "derived sections/direct-image square specification"]
theorem map_isMap (f : X ⟶ Y) (V : Opens Y.carrier) : IsMap f V (map f V) := sorry

/-- The bounded-below derived sections/direct-image map is invertible. -/
@[stacks 01EZ "derived sections/direct-image isomorphism"]
noncomputable instance map_isIso (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIso (map f V) := sorry

/-- Lemma 20.13.1: the natural isomorphism between derived sections on `f ⁻¹ᵁ V`, with scalars
restricted to `Γ(V, 𝒪_Y)`, and derived direct image followed by derived sections on `V`. -/
@[stacks 01EZ "derived sections and direct image"]
noncomputable def iso (f : X ⟶ Y) (V : Opens Y.carrier) : source f V ≅ target f V :=
  asIso (map f V)

/-- The component of the derived sections/direct-image isomorphism at a bounded-below complex. -/
@[stacks 01EZ "derived sections and direct image"]
noncomputable def appIso (f : X ⟶ Y) (V : Opens Y.carrier)
    (K : DerivedCategory.Plus X.Modules) :
    (source f V).obj K ≅ (target f V).obj K :=
  (iso f V).app K

end AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Pushforward
