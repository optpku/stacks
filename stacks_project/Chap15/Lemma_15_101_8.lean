/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Ext
public import ReasLib.Algebra.Homology.DerivedCategory.Ext.Linear
public import ReasLib.Algebra.Module.IdealPower.Quotient.Hom

@[expose] public section

/-!
# Lemma 15.101.8: ideal-power Ext systems

@stack 0EGY
-/

open CategoryTheory
open Ideal.PowerQuotient
open Ideal.PowerQuotient.Hom
open IadicFiniteModuleSystem
open IadicFiniteModuleSystem.Ext

/- Lemma 15.101.8 (0EGY): for finite modules M and N over a Noetherian ring A, the positive
ideal-power system of `Ext^i_A(M, N) / I^n Ext^i_A(M, N)` is isomorphic in the quotient category
to the system of Ext over the reduced rings `A / I^n` and reduced modules.  The Ext systems,
degree-zero normalization, and quotient-ring Hom universal property have separate ReasLib owners;
this file is only the source-facing API boundary.
-/

@[stacks 0EGY "bundled exact ideal-power quotient stage"]
#check @Ideal.PowerQuotient.stageOver
@[stacks 0EGY "scalar-restricted exact ideal-power quotient stage"]
#check @Ideal.PowerQuotient.restrictedStage
@[stacks 0EGY "direct and scalar-restricted exact quotient stages agree"]
#check @Ideal.PowerQuotient.stageIsoRestricted
@[stacks 0EGY "exact ideal-power quotient map"]
#check @Ideal.PowerQuotient.mk
@[stacks 0EGY "Ext quotient system over ideal powers"]
#check @extQuotientSystem
@[stacks 0EGY "reduced-ring Ext system over ideal powers"]
#check @extReductionSystem

/- Degree-zero Ext and the quotient-ring Hom universal property. -/
@[stacks 0EGY "degree-zero Ext and Hom identification"]
#check @CategoryTheory.Abelian.Ext.linearEquiv₀_mk₀
@[stacks 0EGY "base-linear maps into an exact quotient-ring module"]
#check @Ideal.PowerQuotient.Hom.baseHom
@[stacks 0EGY "kernel bound for maps into an exact quotient-ring module"]
#check @Ideal.PowerQuotient.Hom.power_smul_le_ker
@[stacks 0EGY "descent to an exact quotient-ring module"]
#check @Ideal.PowerQuotient.Hom.lift
@[stacks 0EGY "quotient-ring descent on representatives"]
#check @Ideal.PowerQuotient.Hom.lift_mk
@[stacks 0EGY "restriction from an exact quotient-ring Hom"]
#check @Ideal.PowerQuotient.Hom.restrict
@[stacks 0EGY "universal Hom equivalence for an exact quotient-ring module"]
#check @Ideal.PowerQuotient.Hom.equiv
@[stacks 0EGY "linear universal Hom equivalence for an exact quotient-ring module"]
#check @Ideal.PowerQuotient.Hom.linearEquiv

@[stacks 0EGY "bounded representative of the Ext comparison"]
#check @existsComparisonRepresentative

/- Main source statement. -/
@[stacks 0EGY "comparison of Ext systems over ideal-power quotients"]
#check @extQuotientSystem_isomorphic_extReductionSystem
