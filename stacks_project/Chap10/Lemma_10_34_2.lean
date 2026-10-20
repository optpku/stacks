module

public import ReasLib.RingTheory.FiniteType.FieldLocalization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.34.2

@stack 00FY

The source statement is a thin bridge from a finite-type embedding into a field to the canonical
away-localization map. The generic-point and constructibility argument belongs to the proof stage,
so no auxiliary spectrum API is retained here.
-/

/- Lemma 10.34.2: if `R ⊆ K` and `K` is a finite-type `R`-algebra, then for some nonzero
`f : R`, the localization `R_f` is a field and the induced map `R_f → K` is finite. -/
@[stacks 00FY]
#check @Algebra.FiniteType.exists_away_isField_and_finite

@[stacks 00FY "away localization owner"]
#check @Localization.awayLift
@[stacks 00FY "finite type owner"]
#check @Algebra.FiniteType
@[stacks 00FY "finite map owner"]
#check @RingHom.Finite
