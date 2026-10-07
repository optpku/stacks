module

public import ReasLib.RingTheory.Localization.Away.FinitePresentation
import StacksCheckRecall

/-!
# Finite presentation after away localization

@stack 00FG
-/

@[expose] public section

/- **Lemma 10.30.1** ([Stacks tag 00FG](https://stacks.math.columbia.edu/tag/00FG)):
if `R` is a subring of the domain `S` and `S` is of finite type over `R`, then after
inverting suitable nonzero `f : R` and `g : S`, the canonical map `R_f -> S_(fg)` is
finitely presented. -/
@[stacks 00FG]
#check @Algebra.FiniteType.exists_awayMapMul_finitePresentation

@[stacks 00FG "relative away-product map"]
#check @Localization.Away.Relative.mapMul

@[stacks 00FG "finite-presentation predicate"]
#check @RingHom.FinitePresentation
