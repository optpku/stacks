/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Map
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.DerivedValue
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Homology.Below
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical graded-piece comparisons for finite right-derived models

This leaf builds the cochain, derived, and homology comparisons for each graded piece of a mapped
strict filtered-injective resolution.  It also records their forward and inverse naturality.
-/

@[expose] public section

open CategoryTheory ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.GradedPiece

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

omit [HasDerivedCategory B] in
/-- The canonical cochain comparison between a graded piece of the mapped filtered model and
the termwise image of the corresponding graded piece of its resolution. -/
@[stacks 015W "cochain comparison for a finite filtered right-derived model"]
noncomputable abbrev cochainIso (T : A ⥤ₗ B)
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (p : ℤ) :
    (model T R).gradedPiece p ≅
      (CochainComplex.Plus.ι B).obj (T.obj.mapCochainComplexPlus.obj (R.gradedPiece p)) :=
  CochainComplex.FilteredInjectivePlus.Map.GradedPiece.cochainIso T.obj R.complex p

/-- The value of the bounded-below homotopy functor on a resolving graded piece is canonically
the pointwise right-derived value of the source graded piece. -/
@[stacks 015W "derived comparison for a resolved graded piece"]
noncomputable def derivedIso (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (p : ℤ) :
    T.obj.toBoundedBelowDerived.obj (R.gradedPieceHomotopy p) ≅ gradedPiece T K p :=
  Resolution.GradedPiece.valueIso T.obj.toBoundedBelowDerived R p

/-- Homology of a graded piece of the finite filtered model is canonically the homology of the
pointwise right-derived value of the source graded piece. -/
@[stacks 015W "graded-piece comparison for a finite filtered right-derived model"]
noncomputable def homologyIso (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (p n : ℤ) :
    ((model T R).gradedPiece p).homology n ≅
      (DerivedCategory.Plus.homologyFunctor B n).obj (gradedPiece T K p) :=
  (HomologicalComplex.homologyFunctor B (up ℤ) n).mapIso (cochainIso T R p) ≪≫
    Functor.Homotopy.Plus.Homology.homologyIso T.obj (R.gradedPiece p) n ≪≫
      (DerivedCategory.Plus.homologyFunctor B n).mapIso (derivedIso T R p)

/-- The forward graded-piece homology comparison is the composite through the cochain model,
bounded homotopy value, and pointwise derived value. -/
@[simp, stacks 015W "graded-piece comparison for a finite filtered right-derived model"]
theorem homologyIso_hom (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (p n : ℤ) :
    (homologyIso T R p n).hom =
      (HomologicalComplex.homologyFunctor B (up ℤ) n).map (cochainIso T R p).hom ≫
        (Functor.Homotopy.Plus.Homology.homologyIso T.obj (R.gradedPiece p) n).hom ≫
          (DerivedCategory.Plus.homologyFunctor B n).map (derivedIso T R p).hom := sorry

/-- The inverse graded-piece homology comparison is the reverse composite through the pointwise
derived value, bounded homotopy value, and cochain model. -/
@[simp, stacks 015W "inverse graded-piece comparison for a finite filtered right-derived model"]
theorem homologyIso_inv (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (R : Resolution K) (p n : ℤ) :
    (homologyIso T R p n).inv =
      (DerivedCategory.Plus.homologyFunctor B n).map (derivedIso T R p).inv ≫
        (Functor.Homotopy.Plus.Homology.homologyIso T.obj (R.gradedPiece p) n).inv ≫
          (HomologicalComplex.homologyFunctor B (up ℤ) n).map (cochainIso T R p).inv := sorry

omit [HasDerivedCategory B] in
/-- The cochain comparison is natural in maps of strict filtered-injective resolutions. -/
@[reassoc, stacks 015W "naturality of the model graded-piece cochain comparison"]
theorem cochainIso_hom_naturality (T : A ⥤ₗ B)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    FilteredComplex.gradedPieceMap (modelMap T m) p ≫ (cochainIso T S p).hom =
      (cochainIso T R p).hom ≫
        (T.obj.mapHomologicalComplex (up ℤ)).map (m.gradedPieceMap p).hom := sorry

omit [HasDerivedCategory B] in
/-- The inverse cochain comparison is natural in maps of strict filtered-injective
resolutions. -/
@[reassoc, stacks 015W "naturality of the inverse model graded-piece cochain comparison"]
theorem cochainIso_inv_naturality (T : A ⥤ₗ B)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    (T.obj.mapHomologicalComplex (up ℤ)).map (m.gradedPieceMap p).hom ≫
        (cochainIso T S p).inv =
      (cochainIso T R p).inv ≫ FilteredComplex.gradedPieceMap (modelMap T m) p := sorry

/-- The derived graded-piece comparison is natural in maps of strict filtered-injective
resolutions. -/
@[reassoc, stacks 015W "naturality of the resolved graded-piece derived comparison"]
theorem derivedIso_hom_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    T.obj.toBoundedBelowDerived.map (m.gradedPieceHomotopyMap p) ≫
        (derivedIso T S p).hom =
      (derivedIso T R p).hom ≫ gradedPieceMap T f p := sorry

/-- The inverse derived graded-piece comparison is natural in maps of strict
filtered-injective resolutions. -/
@[reassoc, stacks 015W "naturality of the inverse resolved graded-piece comparison"]
theorem derivedIso_inv_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    gradedPieceMap T f p ≫ (derivedIso T S p).inv =
      (derivedIso T R p).inv ≫
        T.obj.toBoundedBelowDerived.map (m.gradedPieceHomotopyMap p) := sorry

/-- The canonical model graded-piece homology comparisons are natural in maps of strict
filtered-injective resolutions. -/
@[reassoc, stacks 015W "naturality of the canonical model graded-piece comparison"]
theorem homologyIso_hom_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p n : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap (modelMap T m) p) n ≫
        (homologyIso T S p n).hom =
      (homologyIso T R p n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map (gradedPieceMap T f p) := sorry

/-- The inverse model graded-piece homology comparisons are natural in maps of strict
filtered-injective resolutions. -/
@[reassoc, stacks 015W "naturality of the inverse model graded-piece comparison"]
theorem homologyIso_inv_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).map (gradedPieceMap T f p) ≫
        (homologyIso T S p n).inv =
      (homologyIso T R p n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap (modelMap T m) p) n := sorry

/-- Conjugating the mapped graded-piece cochain map by the cochain comparison recovers the
filtered model map. -/
@[reassoc, stacks 015W "source-map computation for a graded-piece cochain comparison"]
theorem cochainIso_source_map (T : A ⥤ₗ B)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    (cochainIso T R p).hom ≫
        (T.obj.mapHomologicalComplex (up ℤ)).map (m.gradedPieceMap p).hom ≫
      (cochainIso T S p).inv =
    FilteredComplex.gradedPieceMap (modelMap T m) p := sorry

/-- Conjugating the filtered model map by the inverse graded-piece cochain comparison recovers
the mapped graded-piece cochain map. -/
@[reassoc, stacks 015W "target-map computation for a graded-piece cochain comparison"]
theorem cochainIso_target_map (T : A ⥤ₗ B)
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    (cochainIso T R p).inv ≫
        FilteredComplex.gradedPieceMap (modelMap T m) p ≫
      (cochainIso T S p).hom =
    (T.obj.mapHomologicalComplex (up ℤ)).map (m.gradedPieceMap p).hom := sorry

/-- Conjugating the pointwise derived graded-piece map by the derived comparison recovers the
derived map of the resolved graded piece. -/
@[reassoc, stacks 015W "source-map computation for a derived graded-piece comparison"]
theorem derivedIso_source_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    (derivedIso T R p).hom ≫ gradedPieceMap T f p ≫
      (derivedIso T S p).inv =
    T.obj.toBoundedBelowDerived.map (m.gradedPieceHomotopyMap p) := sorry

/-- Conjugating the resolved graded-piece derived map by the inverse comparison recovers the
pointwise right-derived map. -/
@[reassoc, stacks 015W "target-map computation for a derived graded-piece comparison"]
theorem derivedIso_target_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p : ℤ) :
    (derivedIso T R p).inv ≫
        T.obj.toBoundedBelowDerived.map (m.gradedPieceHomotopyMap p) ≫
      (derivedIso T S p).hom =
    gradedPieceMap T f p := sorry

/-- Conjugating the pointwise derived graded-piece homology map by the homology comparison
recovers the model homology map. -/
@[reassoc, stacks 015W "source-map computation for graded-piece homology comparison"]
theorem homologyIso_source_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p n : ℤ) :
    (homologyIso T R p n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map (gradedPieceMap T f p) ≫
      (homologyIso T S p n).inv =
    HomologicalComplex.homologyMap
      (FilteredComplex.gradedPieceMap (modelMap T m) p) n := sorry

/-- Conjugating the model graded-piece homology map by the inverse comparison recovers the
pointwise derived homology map. -/
@[reassoc, stacks 015W "target-map computation for graded-piece homology comparison"]
theorem homologyIso_target_map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S) (p n : ℤ) :
    (homologyIso T R p n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap (modelMap T m) p) n ≫
      (homologyIso T S p n).hom =
    (DerivedCategory.Plus.homologyFunctor B n).map (gradedPieceMap T f p) := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.GradedPiece
