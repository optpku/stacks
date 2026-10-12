/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect.Local
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dualizable locally strictly perfect complexes on ringed sites

For the canonical total tensor product on complexes of modules over a commutative ring sheaf,
local strict perfectness is equivalent to left or right dualizability.  This leaf owns only the
proposition-valued criterion; chosen closed-monoidal duality data live in `Closed`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

noncomputable section

universe u v w

namespace RingedSite.CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

local notation "Cpx" =>
  _root_.CochainComplex (ringedSiteModuleCategory J O) ℤ

/-- Example 21.48.2: a locally strictly perfect complex is right dualizable for the canonical
total tensor product. -/
@[stacks 0FPR "right dualizable"]
theorem IsLocallyStrictlyPerfect.isRightDualizable
    {F : Cpx}
    (hF : IsLocallyStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) F) :
    IsRightDualizable F := sorry

/-- Braided companion: a locally strictly perfect complex is also left dualizable. -/
@[stacks 0FPR "braided left-dualizable companion"]
theorem IsLocallyStrictlyPerfect.isLeftDualizable
    {F : Cpx}
    (hF : IsLocallyStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) F) :
    IsLeftDualizable F := sorry

/-- Lemma 21.48.3: a right-dualizable complex is locally strictly perfect. -/
@[stacks 0FPS "right dualizable criterion"]
theorem isLocallyStrictlyPerfect_of_isRightDualizable
    {F : Cpx} (hF : IsRightDualizable F) :
    IsLocallyStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) F := sorry

/-- Braided companion: a left-dualizable complex is locally strictly perfect. -/
@[stacks 0FPS "braided left-dualizable companion"]
theorem isLocallyStrictlyPerfect_of_isLeftDualizable
    {F : Cpx} (hF : IsLeftDualizable F) :
    IsLocallyStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) F := sorry

/-- Lemma 21.48.3: explicit exact-pairing data make the first complex locally strictly perfect. -/
@[stacks 0FPS "right exact-pairing form"]
theorem IsLocallyStrictlyPerfect.ofExactPairing
    {F G : Cpx} (p : ExactPairing F G) :
    IsLocallyStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) F := sorry

/-- Braided companion: exact-pairing data make the second complex locally strictly perfect. -/
@[stacks 0FPS "braided left exact-pairing companion"]
theorem IsLocallyStrictlyPerfect.ofLeftExactPairing
    {F G : Cpx} (p : ExactPairing G F) :
    IsLocallyStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) F := sorry

/-- Local strict perfectness is equivalent to right dualizability. -/
@[stacks 0FPR "forward implication", stacks 0FPS "reverse implication"]
theorem isLocallyStrictlyPerfect_iff_isRightDualizable (F : Cpx) :
    IsLocallyStrictlyPerfect
        (X := RingedSite.ofCommRingSheaf J O) F ↔
      IsRightDualizable F := sorry

/-- Braided companion: local strict perfectness is equivalent to left dualizability. -/
@[stacks 0FPR "braided forward companion", stacks 0FPS "braided reverse companion"]
theorem isLocallyStrictlyPerfect_iff_isLeftDualizable (F : Cpx) :
    IsLocallyStrictlyPerfect
        (X := RingedSite.ofCommRingSheaf J O) F ↔
      IsLeftDualizable F := sorry

end RingedSite.CochainComplex
