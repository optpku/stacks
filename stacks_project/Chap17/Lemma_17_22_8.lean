module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FinitePresentation.FilteredColimit
import StacksCheckRecall

/-!
# Lemma 17.22.8 compatibility entry point

The reusable owner records the conclusion as `IsFinitelyPresentable`, so every downstream
filtered-colimit comparison for represented Hom functors follows through the standard category
theory API.
-/

@[expose] public section

/- Lemma 17.22.8 (01BS): under the finite quasi-compact-overlap refinement hypothesis, a finitely
presented module sheaf is finitely presentable as an object of the module-sheaf category. -/
@[stacks 01BS]
#check @SheafOfModules.IsFinitePresentation.isFinitelyPresentable
