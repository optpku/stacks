module

public import ReasLib.Algebra.Homology.Koszul.PowerTower
import StacksCheckRecall

/-!
# The powered Koszul inverse system

This chapter file recalls the three source clauses through the canonical powered-Koszul tower in
`ReasLib`.

@stack 0BKC
-/

@[expose] public section

/- Situation 15.92.15 (1) is recalled by the canonical powered-Koszul cochain and derived
inverse systems. -/
@[stacks 0BKC "(1) powered Koszul inverse system"]
#check @KoszulComplex.PowerTower.cochainSystem
#check @KoszulComplex.PowerTower.derivedSystem

/- Situation 15.92.15 (2) is recalled by the canonical degree-zero comparison with the
powered-family quotient tower. -/
@[stacks 0BKC "(2) degree-zero quotient comparison"]
#check @KoszulComplex.PowerTower.Fin.homologyZeroComparison
#check @KoszulComplex.PowerTower.Fin.cochainHomologyZeroSystem_isIsomorphic_quotientSystem

/- Situation 15.92.15 (3) is recalled by the canonical compatible unit of the powered-Koszul
cochain inverse system. -/
@[stacks 0BKC "(3) compatible unit system"]
#check @KoszulComplex.PowerTower.Fin.unit
