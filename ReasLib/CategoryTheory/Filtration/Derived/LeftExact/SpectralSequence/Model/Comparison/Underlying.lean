module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.DerivedValue
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Homology.Below
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical underlying comparisons for finite right-derived models

This leaf compares homology of the underlying complex of a mapped strict filtered-injective model
with homology of the pointwise right-derived value.  Forward and inverse naturality are exposed as
separate computation rules.
-/

@[expose] public section

open CategoryTheory ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.Underlying

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- The value of the bounded-below homotopy functor on the underlying resolving complex is
canonically the pointwise right-derived value of the source underlying complex. -/
@[stacks 015W "derived comparison for an underlying resolution"]
noncomputable def derivedIso (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) :
    T.obj.toBoundedBelowDerived.obj R.underlyingHomotopy ≅ underlying T K :=
  Resolution.Underlying.valueIso T.obj.toBoundedBelowDerived R

/-- Homology of the underlying finite filtered model is canonically the homology of the
pointwise right-derived value of the source underlying complex. -/
@[stacks 015W "underlying comparison for a finite filtered right-derived model"]
noncomputable def homologyIso (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (n : ℤ) :
    (model T R).underlying.homology n ≅
      (DerivedCategory.Plus.homologyFunctor B n).obj (underlying T K) :=
  Functor.Homotopy.Plus.Homology.homologyIso T.obj R.underlying n ≪≫
    (DerivedCategory.Plus.homologyFunctor B n).mapIso (derivedIso T R)

/-- The forward underlying homology comparison is the composite through the bounded homotopy
value and the pointwise derived value. -/
@[simp, stacks 015W "underlying comparison for a finite filtered right-derived model"]
theorem homologyIso_hom (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (n : ℤ) :
    (homologyIso T R n).hom =
      (Functor.Homotopy.Plus.Homology.homologyIso T.obj R.underlying n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map (derivedIso T R).hom := sorry

/-- The inverse underlying homology comparison is the reverse composite through the pointwise
derived value and the bounded homotopy value. -/
@[simp, stacks 015W "inverse underlying comparison for a finite filtered right-derived model"]
theorem homologyIso_inv (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (n : ℤ) :
    (homologyIso T R n).inv =
      (DerivedCategory.Plus.homologyFunctor B n).map (derivedIso T R).inv ≫
        (Functor.Homotopy.Plus.Homology.homologyIso T.obj R.underlying n).inv := sorry

/-- The derived underlying comparison is natural in maps of strict filtered-injective
resolutions. -/
@[reassoc, stacks 015W "naturality of the resolved underlying derived comparison"]
theorem derivedIso_hom_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) :
    T.obj.toBoundedBelowDerived.map m.underlyingHomotopyMap ≫ (derivedIso T S).hom =
      (derivedIso T R).hom ≫ underlyingMap T f := sorry

/-- The inverse derived underlying comparison is natural in maps of strict
filtered-injective resolutions. -/
@[reassoc, stacks 015W "naturality of the inverse resolved underlying comparison"]
theorem derivedIso_inv_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) :
    underlyingMap T f ≫ (derivedIso T S).inv =
      (derivedIso T R).inv ≫
        T.obj.toBoundedBelowDerived.map m.underlyingHomotopyMap := sorry

/-- The canonical model underlying homology comparisons are natural in maps of strict
filtered-injective resolutions. -/
@[reassoc, stacks 015W "naturality of the canonical model underlying comparison"]
theorem homologyIso_hom_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (n : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap T m)) n ≫
        (homologyIso T S n).hom =
      (homologyIso T R n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map (underlyingMap T f) := sorry

/-- The inverse model underlying homology comparisons are natural in maps of strict
filtered-injective resolutions. -/
@[reassoc, stacks 015W "naturality of the inverse model underlying comparison"]
theorem homologyIso_inv_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).map (underlyingMap T f) ≫
        (homologyIso T S n).inv =
      (homologyIso T R n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap T m)) n := sorry

/-- Conjugating the pointwise underlying derived map by the derived comparison recovers the map
of the resolved underlying complex. -/
@[reassoc, stacks 015W "source-map computation for an underlying derived comparison"]
theorem derivedIso_source_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) :
    (derivedIso T R).hom ≫ underlyingMap T f ≫ (derivedIso T S).inv =
      T.obj.toBoundedBelowDerived.map m.underlyingHomotopyMap := sorry

/-- Conjugating the resolved underlying derived map by the inverse comparison recovers the
pointwise right-derived map. -/
@[reassoc, stacks 015W "target-map computation for an underlying derived comparison"]
theorem derivedIso_target_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) :
    (derivedIso T R).inv ≫
        T.obj.toBoundedBelowDerived.map m.underlyingHomotopyMap ≫
      (derivedIso T S).hom = underlyingMap T f := sorry

/-- Conjugating the pointwise underlying derived homology map by the homology comparison recovers
the model homology map. -/
@[reassoc, stacks 015W "source-map computation for underlying homology comparison"]
theorem homologyIso_source_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (n : ℤ) :
    (homologyIso T R n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map (underlyingMap T f) ≫
      (homologyIso T S n).inv =
    HomologicalComplex.homologyMap
      (FilteredComplex.underlyingMap (modelMap T m)) n := sorry

/-- Conjugating the model underlying homology map by the inverse comparison recovers the
pointwise derived homology map. -/
@[reassoc, stacks 015W "target-map computation for underlying homology comparison"]
theorem homologyIso_target_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (n : ℤ) :
    (homologyIso T R n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap T m)) n ≫
      (homologyIso T S n).hom =
    (DerivedCategory.Plus.homologyFunctor B n).map (underlyingMap T f) := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.Underlying
