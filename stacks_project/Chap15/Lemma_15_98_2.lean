/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.PseudoCoherent

@[expose] public section

/-!
# Pseudo-coherent limits of ideal-power towers

The mathematical owners for Lemma 15.98.2 live in ReasLib; this file records the source-facing
specializations without rebuilding quotient systems, scalar restrictions, or limit models.

@stack 09AV
-/

/- Lemma 15.98.2 (1) (09AV): an adic homotopy limit with pseudo-coherent first stage and
Cartesian transition comparisons is pseudo-coherent. -/
@[stacks 09AV "Lemma 15.98.2 (1), pseudo-coherent ideal-power limit"]
#check @CategoryTheory.ModuleCat.IdealPowerTower.PseudoCoherent.limit

/- Lemma 15.98.2 (2) (09AV): the same homotopy limit is derived complete. -/
@[stacks 09AV "Lemma 15.98.2 (2), derived-complete ideal-power limit"]
#check fun {A : Type*} [CommRing A] {I : Ideal A} [IsAdicComplete I A]
    (T : CategoryTheory.ModuleCat.IdealPowerTower I)
    (_ : CategoryTheory.DerivedCategory.IsPseudoCoherent (T.obj 0))
    (_ : CategoryTheory.ModuleCat.DerivedTower.IsCartesian T)
    {K : DerivedCategory (ModuleCat A)}
    (hK : CategoryTheory.HomotopyLimit.IsOf T.toBase K) ↦
  CategoryTheory.ModuleCat.IdealPowerTower.limit_isDerivedComplete T hK

/- Lemma 15.98.2 (3) (09AV): its canonical derived base-change map to every quotient stage is
an isomorphism. -/
@[stacks 09AV "Lemma 15.98.2 (3), ideal-power limit base change"]
#check @CategoryTheory.ModuleCat.IdealPowerTower.PseudoCoherent.Limit.baseChangeMap_isIso
