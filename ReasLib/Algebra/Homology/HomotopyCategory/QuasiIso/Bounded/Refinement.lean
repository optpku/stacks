/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.EventualHomology
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso.Bounded
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Final
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Refining quasi-isomorphisms by one-sided bounded complexes

The inclusions `K⁺(A) ⥤ K(A)` and `K⁻(A) ⥤ K(A)` have different directional refinement
properties.  Lower truncation gives target refinements for the first inclusion, while upper
truncation gives source refinements for the second.  Registering precisely these two properties
makes the induced denominator and localization-comma functors final or initial automatically.
-/

@[expose] public section

open ComplexShape

universe v u

namespace CategoryTheory.HomotopyCategory.Plus.Ambient

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The localizer morphism from bounded-below homotopy complexes to the ambient homotopy
category.  The `Ambient` namespace distinguishes it from Mathlib's injective-object localizer
morphism. -/
@[stacks 05RV "bounded-below ambient localizer morphism"]
abbrev localizerMorphism :
    LocalizerMorphism (HomotopyCategory.Plus.quasiIso A)
      (HomotopyCategory.quasiIso A (up ℤ)) :=
  fullSubcategoryLocalizerMorphism (HomotopyCategory.plus A)
    (HomotopyCategory.quasiIso A (up ℤ))

/-- A quasi-isomorphism from a bounded-below complex can be followed by a quasi-isomorphism into
another bounded-below complex. -/
@[stacks 05RV "bounded-below target quasi-isomorphism refinement"]
theorem exists_quasiIso_to (X : HomotopyCategory.Plus A)
    {Y : HomotopyCategory A (up ℤ)} (s : X.obj ⟶ Y)
    (hs : HomotopyCategory.quasiIso A (up ℤ) s) :
    ∃ (Z : HomotopyCategory.Plus A) (t : Y ⟶ Z.obj),
      HomotopyCategory.quasiIso A (up ℤ) t := sorry

/-- The bounded-below ambient localizer has target refinements.  Consequently its induced target
denominator and localization costructured-arrow functors are final. -/
instance hasTargetRefinements :
    LocalizerMorphism.HasTargetRefinements (localizerMorphism A) := sorry

variable (X : HomotopyCategory.Plus A)

#synth LocalizerMorphism.HasTargetRefinements (localizerMorphism A)
#synth Functor.Final ((localizerMorphism A).targetDenominators X)
#synth Functor.Final ((localizerMorphism A).costructuredArrow X)


end CategoryTheory.HomotopyCategory.Plus.Ambient

namespace CategoryTheory.HomotopyCategory.Minus.Ambient

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The localizer morphism from bounded-above homotopy complexes to the ambient homotopy
category. -/
@[stacks 05RV "bounded-above ambient localizer morphism"]
abbrev localizerMorphism :
    LocalizerMorphism (HomotopyCategory.Minus.quasiIso A)
      (HomotopyCategory.quasiIso A (up ℤ)) :=
  fullSubcategoryLocalizerMorphism (HomotopyCategory.minus A)
    (HomotopyCategory.quasiIso A (up ℤ))

/-- A quasi-isomorphism into a bounded-above complex can be preceded by a quasi-isomorphism from
another bounded-above complex. -/
@[stacks 05RV "bounded-above source quasi-isomorphism refinement"]
theorem exists_quasiIso_from (X : HomotopyCategory.Minus A)
    {Y : HomotopyCategory A (up ℤ)} (s : Y ⟶ X.obj)
    (hs : HomotopyCategory.quasiIso A (up ℤ) s) :
    ∃ (Z : HomotopyCategory.Minus A) (t : Z.obj ⟶ Y),
      HomotopyCategory.quasiIso A (up ℤ) t := sorry

/-- The bounded-above ambient localizer has source refinements.  Consequently its induced source
denominator and localization structured-arrow functors are initial. -/
instance hasSourceRefinements :
    LocalizerMorphism.HasSourceRefinements (localizerMorphism A) := sorry

variable (X : HomotopyCategory.Minus A)

#synth LocalizerMorphism.HasSourceRefinements (localizerMorphism A)
#synth Functor.Initial ((localizerMorphism A).sourceDenominators X)
#synth Functor.Initial ((localizerMorphism A).structuredArrow X)


end CategoryTheory.HomotopyCategory.Minus.Ambient
