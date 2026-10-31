/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Construction
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets.Value
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison data for finite filtered right-derived models

This file is a reusable leaf of the finite filtered right-derived spectral-sequence API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace Model

/-- Chosen cohomology comparisons between a finite filtered-injective model and the pointwise
right-derived values of the original graded pieces and underlying complex. -/
@[stacks 015W "cohomology comparison for a finite filtered right-derived model"]
structure Comparison (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (R : Resolution K) where
  /-- Comparison on every graded piece and in every cohomological degree. -/
  gradedPieceIso : ∀ p n : ℤ,
    ((model T R).gradedPiece p).homology n ≅
      (DerivedCategory.Plus.homologyFunctor B n).obj (gradedPiece T K p)
  /-- Comparison on the underlying complex in every cohomological degree. -/
  underlyingIso : ∀ n : ℤ,
    (model T R).underlying.homology n ≅
      (DerivedCategory.Plus.homologyFunctor B n).obj (underlying T K)

/-- Every strict finite filtered-injective resolution admits model cohomology comparisons. -/
@[stacks 015W "cohomology comparison for a finite filtered right-derived model"]
theorem Comparison.nonempty (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} (R : Resolution K) :
    Nonempty (Comparison T R) := sorry

namespace Comparison

/-- Compatibility of finite model comparisons along a morphism of strict filtered-injective
resolutions. -/
@[stacks 015W "naturality of finite filtered right-derived model comparisons"]
structure IsCompatible (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Resolution.Map f R S)
    (P : Comparison T R) (Q : Comparison T S) : Prop where
  /-- Naturality on every graded piece and in every cohomological degree. -/
  gradedPieceSq : ∀ p n : ℤ,
    CommSq
      (HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap (modelMap T m) p) n)
      (P.gradedPieceIso p n).hom (Q.gradedPieceIso p n).hom
      ((DerivedCategory.Plus.homologyFunctor B n).map (gradedPieceMap T f p))
  /-- Naturality on the underlying complexes in every cohomological degree. -/
  underlyingSq : ∀ n : ℤ,
    CommSq
      (HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap (modelMap T m)) n)
      (P.underlyingIso n).hom (Q.underlyingIso n).hom
      ((DerivedCategory.Plus.homologyFunctor B n).map (underlyingMap T f))

namespace IsCompatible

/-- Identity resolution maps are compatible with every chosen finite model comparison. -/
@[stacks 015W "identity naturality of finite filtered right-derived model comparisons"]
theorem id (T : A ⥤ₗ B) [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)} {R : Resolution K}
    (P : Comparison T R) :
    IsCompatible T (Resolution.Map.id R) P P := by
  constructor
  · intro p n
    constructor
    dsimp only [modelMap, Resolution.Map.id, FilteredComplex.gradedPieceMap, gradedPieceMap]
    simp only [Functor.map_id, HomologicalComplex.homologyMap_id, Category.id_comp,
      Category.comp_id]
  · intro n
    constructor
    dsimp only [modelMap, Resolution.Map.id, FilteredComplex.underlyingMap, underlyingMap]
    simp only [Functor.map_id, HomologicalComplex.homologyMap_id, Category.id_comp,
      Category.comp_id]

/-- Compatibility of finite model comparisons is preserved by composition. -/
@[stacks 015W "composition of finite filtered right-derived model comparisons"]
theorem comp (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category A)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {U : Resolution M} {m : Resolution.Map f R S} {n : Resolution.Map g S U}
    {P : Comparison T R} {Q : Comparison T S} {V : Comparison T U}
    (h : IsCompatible T m P Q) (k : IsCompatible T n Q V) :
    IsCompatible T (Resolution.Map.comp m n) P V := by
  constructor
  · intro p i
    simpa only [modelMap, Resolution.Map.comp, FilteredComplex.gradedPieceMap, gradedPieceMap,
      Functor.map_comp, HomologicalComplex.homologyMap_comp] using
      (h.gradedPieceSq p i).horiz_comp (k.gradedPieceSq p i)
  · intro i
    simpa only [modelMap, Resolution.Map.comp, FilteredComplex.underlyingMap, underlyingMap,
      Functor.map_comp, HomologicalComplex.homologyMap_comp] using
      (h.underlyingSq i).horiz_comp (k.underlyingSq i)

/-- Reindexing a resolution map preserves compatibility of finite model comparisons. -/
@[stacks 015W "reindexing finite filtered right-derived model comparisons"]
theorem reindex (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} {m : Resolution.Map f R S}
    {P : Comparison T R} {Q : Comparison T S} (h : f = g)
    (hm : IsCompatible T m P Q) :
    IsCompatible T (Resolution.Map.reindex h m) P Q := by
  cases h
  exact hm

/-- Naturality of a compatible finite model comparison on a graded piece. -/
@[reassoc, stacks 015W
  "graded-piece naturality of finite filtered right-derived model comparisons"]
theorem gradedPiece_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} {m : Resolution.Map f R S}
    {P : Comparison T R} {Q : Comparison T S} (h : IsCompatible T m P Q)
    (p n : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap (modelMap T m) p) n ≫
        (Q.gradedPieceIso p n).hom =
      (P.gradedPieceIso p n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map (gradedPieceMap T f p) :=
  (h.gradedPieceSq p n).w

/-- Naturality of the inverse compatible finite model comparison on a graded piece. -/
@[reassoc, stacks 015W
  "inverse graded-piece naturality of finite filtered right-derived model comparisons"]
theorem gradedPiece_inv_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} {m : Resolution.Map f R S}
    {P : Comparison T R} {Q : Comparison T S} (h : IsCompatible T m P Q)
    (p n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).map (gradedPieceMap T f p) ≫
        (Q.gradedPieceIso p n).inv =
      (P.gradedPieceIso p n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.gradedPieceMap (modelMap T m) p) n :=
  (h.gradedPieceSq p n).vert_inv.w

/-- Naturality of a compatible finite model comparison on underlying complexes. -/
@[reassoc, stacks 015W
  "underlying naturality of finite filtered right-derived model comparisons"]
theorem underlying_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} {m : Resolution.Map f R S}
    {P : Comparison T R} {Q : Comparison T S} (h : IsCompatible T m P Q)
    (n : ℤ) :
    HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap T m)) n ≫
        (Q.underlyingIso n).hom =
      (P.underlyingIso n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map (underlyingMap T f) :=
  (h.underlyingSq n).w

/-- Naturality of the inverse compatible finite model comparison on underlying complexes. -/
@[reassoc, stacks 015W
  "inverse underlying naturality of finite filtered right-derived model comparisons"]
theorem underlying_inv_naturality (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} {m : Resolution.Map f R S}
    {P : Comparison T R} {Q : Comparison T S} (h : IsCompatible T m P Q)
    (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).map (underlyingMap T f) ≫
        (Q.underlyingIso n).inv =
      (P.underlyingIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap (modelMap T m)) n :=
  (h.underlyingSq n).vert_inv.w

/-- Solving the graded-piece comparison square for the finite filtered-model homology map. -/
@[reassoc, stacks 015W
  "inverse graded-piece naturality of finite filtered right-derived model comparisons"]
theorem gradedPiece_naturality_inv (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} {m : Resolution.Map f R S}
    {P : Comparison T R} {Q : Comparison T S} (h : IsCompatible T m P Q)
    (p n : ℤ) :
    (P.gradedPieceIso p n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map (gradedPieceMap T f p) ≫
        (Q.gradedPieceIso p n).inv =
      HomologicalComplex.homologyMap
        (FilteredComplex.gradedPieceMap (modelMap T m) p) n := by
  rw [← Category.assoc, ← (h.gradedPieceSq p n).w, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- Solving the underlying comparison square for the finite filtered-model homology map. -/
@[reassoc, stacks 015W
  "inverse underlying naturality of finite filtered right-derived model comparisons"]
theorem underlying_naturality_inv (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} {m : Resolution.Map f R S}
    {P : Comparison T R} {Q : Comparison T S} (h : IsCompatible T m P Q)
    (n : ℤ) :
    (P.underlyingIso n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map (underlyingMap T f) ≫
        (Q.underlyingIso n).inv =
      HomologicalComplex.homologyMap
        (FilteredComplex.underlyingMap (modelMap T m)) n := by
  rw [← Category.assoc, ← (h.underlyingSq n).w, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end IsCompatible

end Comparison

end Model

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
