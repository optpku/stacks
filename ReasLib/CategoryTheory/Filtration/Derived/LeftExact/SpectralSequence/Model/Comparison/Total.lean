/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Total
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Comparison.Resolution
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets.Abutment
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Total canonical comparisons for finite filtered right-derived models

The canonical homology comparisons attached to individual strict filtered-injective resolutions
assemble into natural isomorphisms on the total resolution category.  Separate graded-piece and
underlying interfaces expose their source and target functors, object and morphism computations,
components, and forward and inverse naturality.
-/

@[expose] public section

open CategoryTheory ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace GradedPiece.Homology

omit [HasDerivedCategory B] in
/-- Degree-`n` homology of the `p`-th graded piece of the mapped model, functorial on total strict
filtered-injective resolutions. -/
@[stacks 015W "graded-piece homology source on total finite filtered resolutions"]
noncomputable abbrev source (T : A ⥤ₗ B) (p n : ℤ) :
    Resolution.Total A ⥤ B :=
  Model.functor T ⋙ FilteredComplex.gradedPieceFunctor p ⋙
    HomologicalComplex.homologyFunctor B (up ℤ) n

/-- Degree-`n` homology of the pointwise right-derived `p`-th graded piece, functorial on total
strict filtered-injective resolutions through their source complexes. -/
@[stacks 015W "graded-piece homology target on total finite filtered resolutions"]
noncomputable abbrev target (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ) :
    Resolution.Total A ⥤ B :=
  Resolution.Total.source A ⋙
    _root_.CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.GradedPiece.functor
      T p ⋙
    DerivedCategory.Plus.homologyFunctor B n

omit [HasDerivedCategory B] in
/-- Object computation for graded-piece homology of the mapped total-resolution model. -/
@[simp, stacks 015W "graded-piece homology source computation on total resolutions"]
theorem source_obj (T : A ⥤ₗ B) (p n : ℤ) (X : Resolution.Total A) :
    (source T p n).obj X = ((model T X.obj).gradedPiece p).homology n := sorry

omit [HasDerivedCategory B] in
/-- Morphism computation for graded-piece homology of the mapped total-resolution model. -/
@[simp, stacks 015W "graded-piece homology source computation on total resolutions"]
theorem source_map (T : A ⥤ₗ B) (p n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (source T p n).map f =
      HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap (modelMap T f.displayed) p) n := sorry

/-- Object computation for graded-piece homology of the pointwise right-derived target. -/
@[simp, stacks 015W "graded-piece homology target computation on total resolutions"]
theorem target_obj (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ)
    (X : Resolution.Total A) :
    (target T p n).obj X =
      (DerivedCategory.Plus.homologyFunctor B n).obj
        (_root_.CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.gradedPiece
          T X.base p) := sorry

/-- Morphism computation for graded-piece homology of the pointwise right-derived target. -/
@[simp, stacks 015W "graded-piece homology target computation on total resolutions"]
theorem target_map (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (target T p n).map f =
      (DerivedCategory.Plus.homologyFunctor B n).map
        (_root_.CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.gradedPieceMap
          T f.base p) := sorry

/-- The objectwise canonical graded-piece homology comparisons are natural on the total strict
resolution category. -/
@[reassoc, stacks 015W "naturality of total graded-piece homology comparisons"]
theorem homologyIso_naturality (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (source T p n).map f ≫ (GradedPiece.homologyIso T Y.obj p n).hom =
      (GradedPiece.homologyIso T X.obj p n).hom ≫ (target T p n).map f := sorry

/-- The canonical natural isomorphism from graded-piece homology of mapped total-resolution
models to homology of the pointwise right-derived graded pieces. -/
@[stacks 015W "total graded-piece homology comparison"]
noncomputable def natIso (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ) :
    source T p n ≅ target T p n :=
  NatIso.ofComponents (fun X ↦ GradedPiece.homologyIso T X.obj p n)
    (homologyIso_naturality T p n)

/-- The forward component of the total graded-piece homology comparison is the canonical
comparison of the stored resolution. -/
@[simp, stacks 015W "component of the total graded-piece homology comparison"]
theorem natIso_hom_app (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ)
    (X : Resolution.Total A) :
    (natIso T p n).hom.app X = (GradedPiece.homologyIso T X.obj p n).hom := sorry

/-- The inverse component of the total graded-piece homology comparison is the inverse canonical
comparison of the stored resolution. -/
@[simp, stacks 015W "inverse component of the total graded-piece homology comparison"]
theorem natIso_inv_app (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ)
    (X : Resolution.Total A) :
    (natIso T p n).inv.app X = (GradedPiece.homologyIso T X.obj p n).inv := sorry

/-- Forward naturality of the bundled total graded-piece homology comparison. -/
@[reassoc, stacks 015W "naturality of the total graded-piece homology comparison"]
theorem natIso_hom_naturality (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (source T p n).map f ≫ (natIso T p n).hom.app Y =
      (natIso T p n).hom.app X ≫ (target T p n).map f := sorry

/-- Inverse naturality of the bundled total graded-piece homology comparison. -/
@[reassoc, stacks 015W "inverse naturality of the total graded-piece homology comparison"]
theorem natIso_inv_naturality (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (target T p n).map f ≫ (natIso T p n).inv.app Y =
      (natIso T p n).inv.app X ≫ (source T p n).map f := sorry

/-- Conjugating the target map by the graded-piece comparison recovers the source map. -/
@[reassoc, stacks 015W "source-map computation for total graded-piece homology comparisons"]
theorem natIso_source_map (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (natIso T p n).hom.app X ≫ (target T p n).map f ≫
        (natIso T p n).inv.app Y =
      (source T p n).map f := sorry

/-- Conjugating the source map by the inverse graded-piece comparison recovers the target map. -/
@[reassoc, stacks 015W "target-map computation for total graded-piece homology comparisons"]
theorem natIso_target_map (T : A ⥤ₗ B) [EnoughInjectives A] (p n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (natIso T p n).inv.app X ≫ (source T p n).map f ≫
        (natIso T p n).hom.app Y =
      (target T p n).map f := sorry

end GradedPiece.Homology

namespace Underlying.Homology

omit [HasDerivedCategory B] in
/-- Homology of the underlying mapped model, functorial on total strict filtered-injective
resolutions. -/
@[stacks 015W "underlying homology source on total finite filtered resolutions"]
noncomputable abbrev source (T : A ⥤ₗ B) (n : ℤ) : Resolution.Total A ⥤ B :=
  Model.functor T ⋙ FilteredComplex.underlyingFunctor ⋙
    HomologicalComplex.homologyFunctor B (up ℤ) n

/-- Homology of the pointwise right-derived underlying complex, functorial on total strict
filtered-injective resolutions through their source complexes. -/
@[stacks 015W "underlying homology target on total finite filtered resolutions"]
noncomputable abbrev target (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ) :
    Resolution.Total A ⥤ B :=
  Resolution.Total.source A ⋙
    _root_.CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Abutment.functor T n

omit [HasDerivedCategory B] in
/-- Object computation for homology of the underlying mapped total-resolution model. -/
@[simp, stacks 015W "underlying homology source computation on total resolutions"]
theorem source_obj (T : A ⥤ₗ B) (n : ℤ) (X : Resolution.Total A) :
    (source T n).obj X = (model T X.obj).underlying.homology n := sorry

omit [HasDerivedCategory B] in
/-- Morphism computation for homology of the underlying mapped total-resolution model. -/
@[simp, stacks 015W "underlying homology source computation on total resolutions"]
theorem source_map (T : A ⥤ₗ B) (n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (source T n).map f =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap (modelMap T f.displayed)) n := sorry

/-- Object computation for homology of the pointwise right-derived underlying target. -/
@[simp, stacks 015W "underlying homology target computation on total resolutions"]
theorem target_obj (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    (X : Resolution.Total A) :
    (target T n).obj X =
      _root_.CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Abutment.obj
        T X.base n := sorry

/-- Morphism computation for homology of the pointwise right-derived underlying target. -/
@[simp, stacks 015W "underlying homology target computation on total resolutions"]
theorem target_map (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (target T n).map f =
      _root_.CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Abutment.map
        T f.base n := sorry

/-- The objectwise canonical underlying homology comparisons are natural on the total strict
resolution category. -/
@[reassoc, stacks 015W "naturality of total underlying homology comparisons"]
theorem homologyIso_naturality (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (source T n).map f ≫ (Underlying.homologyIso T Y.obj n).hom =
      (Underlying.homologyIso T X.obj n).hom ≫ (target T n).map f := sorry

/-- The canonical natural isomorphism from homology of underlying mapped total-resolution models
to homology of the pointwise right-derived underlying complexes. -/
@[stacks 015W "total underlying homology comparison"]
noncomputable def natIso (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ) :
    source T n ≅ target T n :=
  NatIso.ofComponents (fun X ↦ Underlying.homologyIso T X.obj n)
    (homologyIso_naturality T n)

/-- The forward component of the total underlying homology comparison is the canonical comparison
of the stored resolution. -/
@[simp, stacks 015W "component of the total underlying homology comparison"]
theorem natIso_hom_app (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    (X : Resolution.Total A) :
    (natIso T n).hom.app X = (Underlying.homologyIso T X.obj n).hom := sorry

/-- The inverse component of the total underlying homology comparison is the inverse canonical
comparison of the stored resolution. -/
@[simp, stacks 015W "inverse component of the total underlying homology comparison"]
theorem natIso_inv_app (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    (X : Resolution.Total A) :
    (natIso T n).inv.app X = (Underlying.homologyIso T X.obj n).inv := sorry

/-- Forward naturality of the bundled total underlying homology comparison. -/
@[reassoc, stacks 015W "naturality of the total underlying homology comparison"]
theorem natIso_hom_naturality (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (source T n).map f ≫ (natIso T n).hom.app Y =
      (natIso T n).hom.app X ≫ (target T n).map f := sorry

/-- Inverse naturality of the bundled total underlying homology comparison. -/
@[reassoc, stacks 015W "inverse naturality of the total underlying homology comparison"]
theorem natIso_inv_naturality (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (target T n).map f ≫ (natIso T n).inv.app Y =
      (natIso T n).inv.app X ≫ (source T n).map f := sorry

/-- Conjugating the target map by the underlying-homology comparison recovers the source map. -/
@[reassoc, stacks 015W "source-map computation for total underlying homology comparisons"]
theorem natIso_source_map (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (natIso T n).hom.app X ≫ (target T n).map f ≫
        (natIso T n).inv.app Y =
      (source T n).map f := sorry

/-- Conjugating the source map by the inverse underlying-homology comparison recovers the target
map. -/
@[reassoc, stacks 015W "target-map computation for total underlying homology comparisons"]
theorem natIso_target_map (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (natIso T n).inv.app X ≫ (source T n).map f ≫
        (natIso T n).hom.app Y =
      (target T n).map f := sorry

end Underlying.Homology

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model
