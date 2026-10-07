module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.Perfect

@[expose] public section

/-!
# Perfect limits of ideal-power towers

Lemma 15.98.4 is a canonical specialization of the reusable ideal-power tower API.

@stack 09AW
-/

/- Lemma 15.98.4 (1) (09AW): an adic homotopy limit with perfect first stage and Cartesian
transition comparisons is perfect. -/
@[stacks 09AW "Lemma 15.98.4 (1), perfect ideal-power limit"]
#check @CategoryTheory.ModuleCat.IdealPowerTower.Perfect.limit

/- Lemma 15.98.4 (2) (09AW): the same homotopy limit is derived complete. -/
@[stacks 09AW "Lemma 15.98.4 (2), derived-complete ideal-power limit"]
#check fun {A : Type*} [CommRing A] {I : Ideal A} [IsAdicComplete I A]
    (T : CategoryTheory.ModuleCat.IdealPowerTower I)
    (_ : (T.obj 0).IsPerfect) (_ : T.IsCartesian)
    {K : DerivedCategory (ModuleCat A)}
    (hK : CategoryTheory.HomotopyLimit.IsOf T.toBase K) ↦
  CategoryTheory.ModuleCat.IdealPowerTower.limit_isDerivedComplete T hK

/- Lemma 15.98.4 (3) (09AW): its canonical derived base-change map to every quotient stage is
an isomorphism. -/
@[stacks 09AW "Lemma 15.98.4 (3), ideal-power limit base change"]
#check @CategoryTheory.ModuleCat.IdealPowerTower.Perfect.Limit.baseChangeMap_isIso
