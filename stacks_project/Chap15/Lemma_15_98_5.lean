module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.IdealPower.BoundedAbove

@[expose] public section

/-!
# Bounded-above limits of ideal-power towers

Lemma 15.98.5 uses the canonical Noetherian ideal-power specialization and the standard
`DerivedCategory.IsBoundedAbove` predicate.

@stack 09AU
-/

/- Lemma 15.98.5 (1) (09AU): the homotopy limit of the stated Noetherian Cartesian tower is
bounded above. -/
@[stacks 09AU "Lemma 15.98.5 (1), bounded-above ideal-power limit"]
#check @CategoryTheory.ModuleCat.IdealPowerTower.BoundedAbove.limit

/- Lemma 15.98.5 (2) (09AU): the same homotopy limit is derived complete. -/
@[stacks 09AU "Lemma 15.98.5 (2), derived-complete ideal-power limit"]
#check fun {A : Type*} [CommRing A] {I : Ideal A} [IsNoetherianRing A]
    (T : CategoryTheory.ModuleCat.IdealPowerTower I)
    (_ : CategoryTheory.DerivedCategory.IsBoundedAbove (T.obj 0))
    (_ : CategoryTheory.ModuleCat.DerivedTower.IsCartesian T)
    {K : DerivedCategory (ModuleCat A)}
    (hK : CategoryTheory.HomotopyLimit.IsOf T.toBase K) ↦
  CategoryTheory.ModuleCat.IdealPowerTower.limit_isDerivedComplete T hK

/- Lemma 15.98.5 (3) (09AU): its canonical derived base-change map to every quotient stage is
an isomorphism. -/
@[stacks 09AU "Lemma 15.98.5 (3), ideal-power limit base change"]
#check @CategoryTheory.ModuleCat.IdealPowerTower.BoundedAbove.Limit.baseChangeMap_isIso
