module

public import ReasLib.CategoryTheory.Monoidal.Bimod.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.10.1

The reusable owner is the lift of a monoidal adjunction satisfying the projection formula to
right-module categories.  In the localized graded-sheaf application, the right adjoint is
restriction and the explicitly constructed left adjoint is extension by zero.
-/

open CategoryTheory

/- Lemma 24.10.1 (0FRA): extension by zero for modules is left adjoint to restriction. -/
@[stacks 0FRA] #check @Adjunction.rightModuleAdjunction

/- The left adjoint is an explicit functor whose module action is induced by the projection
formula, rather than an abstract choice of a left adjoint. -/
@[stacks 0FRA "module extension by zero"] #check @Adjunction.rightModuleLowerShriek

/- The displayed source bijection is the module-level Hom equivalence of this adjunction. -/
@[stacks 0FRA "module extension-by-zero Hom equivalence"]
#check @Adjunction.rightModuleHomEquiv

/- For a canonical ambient right adjoint, the transported module functor is itself registered as
a right adjoint without a local instance. -/
#check @Adjunction.mapRightModule_isRightAdjoint
