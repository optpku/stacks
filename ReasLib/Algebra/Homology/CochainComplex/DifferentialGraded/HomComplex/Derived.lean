/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.Derived
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.DerivedHom.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.KInjective.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Cohomology.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.FunctorialResolution
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Enriched Hom for Cochain Complexes

Functorial K-injective resolutions supply the simultaneous total right-derived enriched Hom
bifunctor.  This leaf owns both that criterion and the canonical Grothendieck-abelian instance,
independently of any ringed-site presentation.
-/

@[expose] public section

noncomputable section

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe x w v u

namespace CategoryTheory.CochainComplex.Enriched.RHom

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The homotopy-level enriched Hom bifunctor for cochain complexes in `C`. -/
@[stacks 0CS6 "integral cochain derived-Hom source"]
noncomputable abbrev source :=
  Over.RHom.source (R := ℤ) (C := C)

/-- The simultaneous quasi-isomorphism system for both variables of enriched Hom. -/
@[stacks 0CS6 "integral cochain derived-Hom denominators"]
abbrev qis :=
  Over.RHom.qis (R := ℤ) (C := C)

/-- The product localization from enriched cochain homotopy objects to pairs of derived
objects. -/
@[stacks 0CS6 "integral cochain derived-Hom localization"]
noncomputable abbrev localization [HasDerivedCategory.{w} C] :=
  Over.RHom.localization (R := ℤ) (C := C)

/-- The existence condition for simultaneous derived enriched Hom on cochain complexes. -/
@[stacks 0CS6 "existence condition for derived enriched Hom"]
abbrev Has : Prop :=
  Over.RHom.Has (R := ℤ) (C := C)

/-- Objectwise K-injective resolutions give the integral enriched derived-Hom bifunctor. -/
@[stacks 0CS6 "integral derived Hom from K-injective resolutions"]
theorem ofResolutions
    (h : ∀ K : CochainComplex C ℤ,
      Nonempty (_root_.CochainComplex.KInjectiveResolution K)) :
    Has (C := C) := sorry

/-- A functorial K-injective resolution gives the integral enriched derived-Hom bifunctor. -/
@[stacks 0CS6 "integral derived Hom from a functorial K-injective resolution"]
theorem ofFunctorialResolution
    (J : _root_.CochainComplex.KInjectiveResolution.Functorial C) :
    Has (C := C) := sorry

/-- A Grothendieck abelian category has the integral enriched derived-Hom bifunctor. -/
@[stacks 0CS6 "integral derived Hom in a Grothendieck category"]
instance hasRightDerivedFunctor [IsGrothendieckAbelian.{x} C] :
    Has (C := C) := sorry

/-- The `D(ℤ)`-valued derived enriched Hom bifunctor of cochain complexes. -/
@[stacks 0CS6 "derived enriched Hom bifunctor"]
noncomputable abbrev functor [HasDerivedCategory.{w} C]
    [Has (C := C)] :=
  Over.RHom.functor (R := ℤ) (C := C)

/-- The curried cochain-complex `RHom` functor, with the derived source variable first. -/
@[stacks 0CS6 "curried enriched derived Hom for cochain complexes"]
noncomputable abbrev curried [HasDerivedCategory.{w} C]
    [Has (C := C)] :=
  Over.RHom.curried (R := ℤ) (C := C)

/-- The cochain-complex `RHom` functor with fixed derived target and varying source. -/
@[stacks 0CS6 "source-variable enriched derived Hom for cochain complexes"]
noncomputable abbrev sourceFunctor [HasDerivedCategory.{w} C]
    [Has (C := C)] (N : DerivedCategory C) :=
  Over.RHom.sourceFunctor (R := ℤ) (C := C) N

/-- The cochain-complex `RHom` functor with fixed derived source and varying target. -/
@[stacks 0CS6 "target-variable enriched derived Hom for cochain complexes"]
noncomputable abbrev targetFunctor [HasDerivedCategory.{w} C]
    [Has (C := C)] (M : (DerivedCategory C)ᵒᵖ) :=
  Over.RHom.targetFunctor (R := ℤ) (C := C) M

/-- The universal map from enriched Hom on homotopy objects to derived enriched Hom. -/
@[stacks 0CS6 "enriched Hom to derived enriched Hom"]
noncomputable abbrev unit [HasDerivedCategory.{w} C]
    [Has (C := C)] :=
  Over.RHom.unit (R := ℤ) (C := C)

/-- The derived enriched-Hom unit evaluated on a pair of strict cochain complexes. -/
@[stacks 0CS6 "integral strict-complex derived-Hom unit"]
noncomputable abbrev unitApp [HasDerivedCategory.{w} C] [Has (C := C)]
    (M N : CochainComplex C ℤ) :=
  Over.RHom.unitApp (R := ℤ) (C := C) M N

/-- The canonical isomorphism from strict enriched Hom into a K-injective complex to derived
enriched Hom. -/
@[stacks 070Y "K-injective strict model of enriched derived Hom"]
noncomputable def unitAppIsoOfKInjective [HasDerivedCategory.{w} C] [Has (C := C)]
    (M I : CochainComplex C ℤ) [I.IsKInjective] :=
  Over.RHom.unitAppIsoOfKInjective (R := ℤ) (C := C) M I

/-- A K-injective resolution gives the canonical strict Hom-complex model of enriched derived
Hom, expressed using the standard derived-category images of `M` and `N`. -/
@[stacks 0CS6 "K-injective resolution model of enriched derived Hom"]
noncomputable def resolutionModelIso [HasDerivedCategory.{w} C] [Has (C := C)]
    (M : CochainComplex C ℤ) {N : CochainComplex C ℤ}
    (I : _root_.CochainComplex.KInjectiveResolution N) :
    DerivedCategory.Q.obj (DifferentialGradedCategory.homComplex M I.complex) ≅
      (functor (C := C)).obj
        (Opposite.op (DerivedCategory.Q.obj M), DerivedCategory.Q.obj N) :=
  Over.RHom.resolutionModelIso (R := ℤ) (C := C) M I

end CategoryTheory.CochainComplex.Enriched.RHom
