module

public import ReasLib.RingTheory.GlobalDimension.Localization
import StacksCheckRecall

/-!
# Projective and Global Dimension under Localization

@stack 00O8
-/

@[expose] public section

/- Lemma 10.109.13 (1) [stacks 00O8]: localization does not increase the
projective dimension of a module. -/
@[stacks 00O8 "(1)"]
#check @ModuleCat.localizedModule_hasProjectiveDimensionLE

/- Lemma 10.109.13 (2) [stacks 00O8]: localization preserves a global-dimension
bound. -/
@[stacks 00O8 "(2)"]
#check @HasGlobalDimensionLE.localization

/- Canonical numerical, finite-global-dimension, and typeclass views of the two source clauses. -/
@[stacks 00O8 "localized numerical projective dimension"]
#check @ModuleCat.projectiveDimension_le_projectiveDimension_of_isLocalizedModule
@[stacks 00O8 "localized finite global dimension"]
#check @IsFiniteGlobalDimensionRing.localization
@[stacks 00O8 "localized global dimension bound"]
#check @localization_hasGlobalDimensionLE
