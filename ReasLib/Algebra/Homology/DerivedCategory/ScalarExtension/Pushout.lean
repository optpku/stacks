/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Pushout
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Model
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Pushout.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relatively flat models under pushout base change

@stack 0E1U

For a pushout square with flat left edge, a bounded-above complex that is termwise flat over the
base ring computes derived extension along the opposite edge.  This is the change-of-rings bridge
between relative flat models and the ordinary scalar-extension complex.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.ModuleCat.Pushout.DerivedExtension

variable {R A R' A' : Type u}
variable [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
variable [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
variable [IsScalarTower R A A'] [IsScalarTower R R' A']
variable [hpush : Algebra.IsPushout R R' A A']

include hpush

/-- A canonical route comparison certificate is enough to identify the derived-extension
 counit on a bounded-above relatively flat model.  The comparison is the component at
 `DerivedCategory.Q.obj F` of the existing map from the base-ring route to the target-algebra
 route; the bounded-above and relative-flat hypotheses are the data used to compute the former.
 No flatness of the square edge `R → A` is built into this criterion. -/
@[stacks 0E1U "counit criterion from the canonical pushout comparison"]
theorem counitIsIso_of_comparisonApp
    (F : CochainComplex (ModuleCat A) ℤ)
    (hF : CochainComplex.minus (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatOver R)
    (hcomparison : IsIso
      (comparisonApp (R := R) (A := A) (R' := R') (A' := A')
        (DerivedCategory.Q.obj F))) :
    IsIso ((ModuleCat.derivedExtensionComplexCounit (algebraMap A A')).app F) := sorry

variable [Module.Flat R A]

/-- In a pushout square, bounded-above relative flatness of the model makes the derived-extension
comparison invertible. -/
@[stacks 0E1U "relatively flat model under pushout base change"]
theorem counitIsIso
    (F : CochainComplex (ModuleCat A) ℤ)
    (hF : CochainComplex.minus (ModuleCat A) F)
    (hFflat : F.IsTermwiseFlatOver R) :
    IsIso ((ModuleCat.derivedExtensionComplexCounit (algebraMap A A')).app F) := sorry

end CategoryTheory.ModuleCat.Pushout.DerivedExtension
