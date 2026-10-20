module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCriterion.Consequences

import StacksCheckRecall

/-!
# Practical module glueability criteria

The completion, Tor, and flatness consequences of the module Beauville-Laszlo criterion are owned
by `ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCriterion.Consequences`.

@stack 0BNX
-/

-- The two explicit completion maps used in the first three clauses.
@[stacks 0BNX "completion comparison on power torsion"]
#check @completionFPowerTorsionToCompletionTensor

@[stacks 0BNX "completion map on the submodule killed by f"]
#check @fTorsionToAdicCompletion

-- Remark 15.91.11 (1): the completion-tensor injectivity criterion.
@[stacks 0BNX "Remark 15.91.11 (1)"]
#check @isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToCompletionTensor

-- Remark 15.91.11 (1), sufficient condition: injectivity on the submodule killed by `f`.
@[stacks 0BNX "Remark 15.91.11 (1), sufficient condition"]
#check @isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_injective_fTorsionToAdicCompletion

-- Remark 15.91.11 (1), intersection criterion: separated `f`-torsion.
@[stacks 0BNX "Remark 15.91.11 (1), intersection criterion"]
#check @fTorsionToAdicCompletion_injective_iff_torsion_inf_principalPowers_eq_bot

-- Remark 15.91.11 (2): first-Tor vanishing after localization.
@[stacks 0BNX "Remark 15.91.11 (2)"]
#check @isBeauvilleLaszloGlueableAlong_of_torOne_localizedTarget_isZero

-- Remark 15.91.11 (2), equivalent condition: localized Tor vanishing as power torsion.
@[stacks 0BNX "Remark 15.91.11 (2), equivalent condition"]
#check @torOne_extension_isTorsion'_powers_iff_torOne_localizedTarget_isZero

-- Remark 15.91.11 (2), flat special case: flat modules are glueable.
@[stacks 0BNX "Remark 15.91.11 (2), flat special case"]
#check @isBeauvilleLaszloGlueableAlong_of_flat_module

-- Remark 15.91.11 (3): flat extensions make every module glueable.
@[stacks 0BNX "Remark 15.91.11 (3)"]
#check @isBeauvilleLaszloGlueableAlong_of_flat_extension

-- Remark 15.91.11 (3), Noetherian specialization: principal-adic completion.
@[stacks 0BNX "Remark 15.91.11 (3), Noetherian specialization"]
#check @isBeauvilleLaszloGlueableAlong_principalAdicCompletion_of_isNoetherianRing
