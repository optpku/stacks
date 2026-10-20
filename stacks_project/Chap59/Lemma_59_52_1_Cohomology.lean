/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ComplexSystem
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Hypercohomology.Pullback
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-! Source-facing checks for the derived étale hypercohomology API. -/

set_option pp.universes true in
#check @CategoryTheory.siteAbelianSectionsDerived
#check @CategoryTheory.Functor.sheafAdjunctionContinuous
#check @CategoryTheory.sheafSectionsNatIsoEvaluation
#check @CategoryTheory.Functor.RightDerived.Cochain.unit
#check @AlgebraicGeometry.Scheme.Etale.AbelianSheafComplexSystem.conePullbackComplex
#check @AlgebraicGeometry.Scheme.Etale.hypercohomologyFunctor
#check @AlgebraicGeometry.Scheme.Etale.etaleHypercohomology
#check @AlgebraicGeometry.Scheme.Etale.etaleHypercohomology.map
#check @AlgebraicGeometry.Scheme.Etale.etaleHypercohomology_obj
#check @AlgebraicGeometry.Scheme.Etale.inverseImageComplexFunctor
#check @AlgebraicGeometry.Scheme.Etale.inverseImageComplex
#check @AlgebraicGeometry.Scheme.Etale.inverseImageComplexFunctor_invertsQuasiIso
#check @AlgebraicGeometry.Scheme.Etale.derivedInverseImage
#check @AlgebraicGeometry.Scheme.Etale.derivedInverseImageCompQIso
#check @AlgebraicGeometry.Scheme.Etale.sectionsPullback
#check @AlgebraicGeometry.Scheme.Etale.derivedSectionsPullback
#check @AlgebraicGeometry.Scheme.Etale.derivedSectionsPullback_fac
#check @AlgebraicGeometry.Scheme.Etale.hypercohomologyPullback
