module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
import StacksCheckRecall

/-!
# Finite presentation and filtered colimits of modules

@stack 0G8P
-/

@[expose] public section

/- Lemma 10.11.4: an `R`-module is finitely presented exactly when its represented functor
preserves filtered colimits. The two canonical equivalences below meet at the bundled predicate
`IsFinitelyPresentable`. -/

@[stacks 0G8P "finite presentation iff bundled finite presentability"]
#check @ModuleCat.isFinitelyPresentable_iff_finitePresentation

@[stacks 0G8P "bundled finite presentability iff filtered-colimit preservation"]
#check @CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits
