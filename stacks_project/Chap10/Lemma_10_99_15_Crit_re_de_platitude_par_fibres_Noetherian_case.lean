module

public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.Noetherian
import StacksCheckRecall

/-!
# Critere de platitude par fibres: Noetherian case

@stack 00MP

The reusable statement is owned by the closed-fiber local-criterion API.  Its
canonical `RestrictScalars` views replace the source presentation's redundant
compatible module structures.
-/

@[expose] public section

@[stacks 00MP "module clause"]
#check @Module.Flat.ClosedFiber.of_noetherian

@[stacks 00MP "ring-map clause"]
#check @RingHom.Flat.ClosedFiber.of_noetherian
