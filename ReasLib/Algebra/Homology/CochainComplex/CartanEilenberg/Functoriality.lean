/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Basic
public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.Functor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial comparisons for Cartan--Eilenberg resolutions

This file packages the four resolution-to-column comparisons after applying an additive functor,
together with their induced homology comparisons.
-/

open CategoryTheory

noncomputable section

universe v u v' u'

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K : CochainComplex.Plus A}

section Functoriality

variable {B : Type u'} [Category.{v'} B] [Preadditive B]

/-- The double complex obtained by applying an additive functor in both complex directions. -/
@[stacks 015J "the termwise image of a Cartan-Eilenberg double complex"]
abbrev mapBicomplex (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] :
    HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (F.mapHomologicalComplex₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj I.bicomplex

namespace Column

/-- Applying an additive functor to the comparison from a chosen column resolution to its
Cartan--Eilenberg column. -/
@[stacks 015J "the mapped Cartan-Eilenberg column comparison"]
noncomputable abbrev mapResolutionIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (p : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.columnResolution p).cochainComplex ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.column p) :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (Column.resolutionIso I p)

end Column

namespace Cycles

/-- Applying an additive functor to the comparison from a chosen cycles resolution to its
cycles column. -/
@[stacks 015J "the mapped Cartan-Eilenberg cycles comparison"]
noncomputable abbrev mapResolutionIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (p : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.cyclesResolution p).cochainComplex ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.cyclesColumn p) :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (Cycles.resolutionIso I p)

end Cycles

namespace Image

/-- Applying an additive functor to the comparison from a chosen image resolution to its image
column. -/
@[stacks 015J "the mapped Cartan-Eilenberg image comparison"]
noncomputable abbrev mapResolutionIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (p : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.imageResolution p).cochainComplex ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.imageColumn p) :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (Image.resolutionIso I p)

end Image

namespace Homology

/-- Applying an additive functor to the comparison from a chosen cohomology resolution to its
horizontal-homology column. -/
@[stacks 015J "the mapped Cartan-Eilenberg homology comparison"]
noncomputable abbrev mapResolutionIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (p : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.homologyResolution p).cochainComplex ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.homologyColumn p) :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (Homology.resolutionIso I p)

end Homology

end Functoriality

section HomologyFunctoriality

variable {B : Type u'} [Category.{v'} B] [Preadditive B] [CategoryWithHomology B]

namespace Column

/-- After applying an additive functor, the chosen column resolution and the actual column have
canonically isomorphic cohomology in every degree. -/
noncomputable abbrev mapResolutionHomologyIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (I.columnResolution p).cochainComplex).homology q ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.column p)).homology q :=
  (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q).mapIso
    (Column.mapResolutionIso I F p)

end Column

namespace Cycles

/-- After applying an additive functor, the chosen cycles resolution and the cycles column have
canonically isomorphic cohomology in every degree. -/
noncomputable abbrev mapResolutionHomologyIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (I.cyclesResolution p).cochainComplex).homology q ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.cyclesColumn p)).homology q :=
  (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q).mapIso
    (Cycles.mapResolutionIso I F p)

end Cycles

namespace Image

/-- After applying an additive functor, the chosen image resolution and the image column have
canonically isomorphic cohomology in every degree. -/
noncomputable abbrev mapResolutionHomologyIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (I.imageResolution p).cochainComplex).homology q ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.imageColumn p)).homology q :=
  (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q).mapIso
    (Image.mapResolutionIso I F p)

end Image

namespace Homology

/-- After applying an additive functor, the chosen homology resolution and the horizontal-homology
column have canonically isomorphic cohomology in every degree. -/
noncomputable abbrev mapResolutionHomologyIso
    (I : CartanEilenbergResolution K) (F : A ⥤ B) [F.Additive] (p q : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (I.homologyResolution p).cochainComplex).homology q ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.homologyColumn p)).homology q :=
  (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q).mapIso
    (Homology.mapResolutionIso I F p)

end Homology

end HomologyFunctoriality

end CochainComplex.CartanEilenbergResolution
