module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import Mathlib.Tactic.CrossRefAttribute

/-!
# The category of derived-complete modules

@stack 0GLP
@stack 091U

This leaf owns the categorical consequences of the derived-completeness predicate.  The predicate
itself and the derived-completion reflector live in `Completeness`; this file exposes the module
subcategory and its reusable exactness, limit, colimit, and adjunction interfaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat.DerivedComplete

variable {A : Type u} [CommRing A]

/-! The following abbreviations keep categorical statements at the level of the mathematical
subcategory rather than repeating the full object-property expression. -/

/-- The object property of `A`-modules that are derived complete with respect to `I`. -/
@[stacks 0GLP "derived-complete module property"]
abbrev property (I : Ideal A) : ObjectProperty (ModuleCat A) :=
  ModuleCat.derivedCompleteObjectProperty I

/-- The full subcategory of `A`-modules derived complete with respect to `I`. -/
@[stacks 0GLP "the category of derived-complete modules"]
abbrev category (I : Ideal A) := (property I).FullSubcategory

/-- The inclusion of derived-complete modules into all `A`-modules. -/
@[stacks 0GLP "inclusion of derived-complete modules"]
abbrev inclusion (I : Ideal A) : category I ⥤ ModuleCat A := (property I).ι

/-- Explicit reflector data for the inclusion of derived-complete `A`-modules.  This remains an
ordinary structure argument because a left adjoint is a choice, not canonical instance data. -/
@[stacks 0GLP "reflector onto derived-complete modules"]
abbrev Reflector (I : Ideal A) := ObjectProperty.Reflector (property I)

/-! ### Exact and limit structure -/

/-- Stacks `0GLP`: derived-complete modules form a weak Serre subcategory. -/
@[stacks 0GLP "derived-complete modules form a weak Serre subcategory"]
instance isWeakSerreClass (I : Ideal A) :
    ObjectProperty.IsWeakSerreClass (property I) := sorry
-- Proof strategy: apply localization-away derived Hom to a short exact sequence and use
-- the resulting long exact sequence to prove closure under kernels, cokernels, and extensions.

/-- Stacks `0GLP`: the derived-complete module category is abelian. -/
@[stacks 0GLP "the category of derived-complete modules is abelian"]
instance abelian (I : Ideal A) : Abelian (category I) := inferInstance

/-- Stacks `0GLP`: the derived-complete module category has arbitrary limits. -/
@[stacks 0GLP "arbitrary limits of derived-complete modules"]
instance hasLimits (I : Ideal A) : HasLimits (category I) := sorry
-- Proof strategy: construct limits through the full-subcategory limit API; products and
-- equalizers stay derived complete because the localization-away Hom predicates commute
-- with the corresponding limits.

/- The inclusion is exact as a bundled Mathlib functor property. -/
/-- Stacks `0GLP`: the inclusion of derived-complete modules is exact. -/
@[stacks 0GLP "exact inclusion of derived-complete modules"]
theorem inclusion_exact (I : Ideal A) :
    exactFunctor (category I) (ModuleCat A) (inclusion I) := sorry
-- Proof strategy: invoke exactness of the inclusion of a weak Serre full subcategory, using
-- `isWeakSerreClass I` and the ambient abelian structure on `ModuleCat A`.

/- The ambient and subcategory limits are represented at the same universe level, as in `HasLimits`.
-/
/-- Stacks `0GLP`: the inclusion commutes with arbitrary limits. -/
@[stacks 0GLP "the derived-complete inclusion preserves limits"]
instance inclusion_preservesLimits (I : Ideal A) :
    PreservesLimitsOfSize (inclusion I) := sorry
-- Proof strategy: use the full-subcategory limit construction from `hasLimits I` and show
-- its cone is the ambient limit cone after applying the inclusion.

/-! ### Finite-generation consequences -/

/-- Stacks `0GLP`: if `I` is finitely generated, derived-complete modules have arbitrary
colimits. -/
@[stacks 0GLP "arbitrary colimits for finitely generated derived completeness"]
theorem hasColimits (I : Ideal A) (hI : I.FG) : HasColimits (category I) := sorry
-- Proof strategy: use the reflector supplied by finite generation; a reflective full
-- subcategory of the cocomplete module category inherits all colimits.

/-- Stacks `0GLP`: if `I` is finitely generated, the inclusion of derived-complete modules has a
left adjoint. -/
@[stacks 0GLP "left adjoint to the derived-complete inclusion"]
theorem inclusion_isRightAdjoint (I : Ideal A) (hI : I.FG) :
    Functor.IsRightAdjoint (inclusion I) := sorry
-- Proof strategy: take the finite-generation derived-completion reflector from the canonical
-- completeness owner and identify its fixed objects with `property I`.

/-- Stacks `0GLP`: finite generation gives explicit reflector data for the derived-complete module
subcategory. -/
@[stacks 0GLP "existence of a derived-complete module reflector"]
theorem existsReflector (I : Ideal A) (hI : I.FG) : Nonempty (Reflector I) := sorry
-- Proof strategy: apply `ObjectProperty.Reflector.ofIsRightAdjoint` to
-- `inclusion_isRightAdjoint I hI` and package the resulting reflector as a `Nonempty` witness.

/-- A selected reflector onto the derived-complete module category.  The finite-generation proof
is kept explicit because it is the mathematical input guaranteeing existence of the left
adjoint. -/
@[stacks 0GLP "selected reflector onto derived-complete modules"]
noncomputable def chosenReflector (I : Ideal A) (hI : I.FG) : Reflector I :=
  ObjectProperty.Reflector.ofIsRightAdjoint (property I)
    (inclusion_isRightAdjoint I hI)

/-- The selected reflector carries the expected adjunction with the inclusion. -/
@[stacks 0GLP "selected derived-complete module reflector specification"]
noncomputable def chosenReflector_spec (I : Ideal A) (hI : I.FG) :
    (chosenReflector I hI).toFullSubcategory ⊣ inclusion I :=
  (chosenReflector I hI).adjunction

/-- The left-adjoint functor of the selected reflector is canonically isomorphic to that of any
other reflector onto the same derived-complete module category. -/
@[stacks 0GLP "independence of the selected derived-complete module reflector"]
noncomputable def chosenReflectorIso (I : Ideal A) (hI : I.FG) (R : Reflector I) :
    (chosenReflector I hI).toFullSubcategory ≅ R.toFullSubcategory :=
  (chosenReflector I hI).adjunction.leftAdjointUniq R.adjunction

/-- The ambient reflection endofunctors induced by the selected reflector and any other
reflector are canonically isomorphic. -/
@[stacks 0GLP "independence of the selected derived-complete module reflection"]
noncomputable def chosenReflectionIso (I : Ideal A) (hI : I.FG) (R : Reflector I) :
    (chosenReflector I hI).reflection ≅ R.reflection :=
  Functor.isoWhiskerRight (chosenReflectorIso I hI R) (inclusion I)

namespace chosenReflectionIso

/-- The comparison with another reflector identifies their universal reflection maps. -/
@[stacks 0GLP "independence of the derived-complete module reflection unit"]
theorem unit (I : Ideal A) (hI : I.FG) (R : Reflector I) :
    (chosenReflector I hI).unit ≫ (chosenReflectionIso I hI R).hom = R.unit := sorry
-- Proof strategy: unfold `chosenReflectionIso` and use the unit compatibility theorem for
-- `Adjunction.leftAdjointUniq`, then reassociate whiskering with the inclusion.

end chosenReflectionIso

end ModuleCat.DerivedComplete

namespace DerivedCategory.DerivedComplete

variable {A : Type u} [CommRing A]

/-! The derived-category side of the 091U statement is exposed separately from the module
subcategory.  This keeps the cohomology-in construction reusable for any coefficient property
which later acquires the same comparison theorem. -/

/--
 * Lemma 15.92.6 (Stacks `091U`) (2): the derived-complete derived objects are precisely the
 * objects whose cohomology modules are derived complete.
-/
@[stacks 091U "derived completeness detected on cohomology"]
theorem property_eq_cohomologyIn (I : Ideal A) :
    DerivedCategory.derivedCompleteObjectProperty I =
      DerivedCategory.cohomologyIn (ModuleCat.derivedCompleteObjectProperty I) := sorry
-- Proof strategy: ext a derived object and apply the canonical theorem that derived
-- completeness is equivalent to derived completeness of every cohomology module.

/--
 * The full subcategory of derived-complete objects, presented through the canonical
 * cohomology-in construction.
-/
@[stacks 091U "derived-complete derived-category subcategory"]
abbrev category (I : Ideal A) :=
  (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory

/--
 * The same full subcategory presented by degreewise cohomology membership.
-/
@[stacks 091U "cohomology-presented derived-complete subcategory"]
abbrev cohomologyCategory (I : Ideal A) :=
  (DerivedCategory.cohomologyIn (ModuleCat.derivedCompleteObjectProperty I)).FullSubcategory

/--
 * Membership in the derived-complete full subcategory is equivalent to membership in its
 * cohomology-in presentation.
-/
@[stacks 091U "derived-complete cohomology-in membership"]
theorem mem_iff (I : Ideal A) (K : DerivedCategory (ModuleCat A)) :
    K.IsDerivedCompleteWithRespectTo I ↔
      DerivedCategory.cohomologyIn (ModuleCat.derivedCompleteObjectProperty I) K := sorry
-- Proof strategy: evaluate `property_eq_cohomologyIn I` at `K` and unfold the two object
-- properties only at the final membership step.

end DerivedCategory.DerivedComplete

end
