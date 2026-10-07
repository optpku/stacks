module

public import ReasLib.Algebra.Module.DifferentialOperator.FiniteOrder
public import ReasLib.Algebra.Module.DifferentialOperator.FormallyEtale
import StacksCheckRecall

@[expose] public section

/-!
Remark 10.150.9 (Tag 0H95): finite-order differential endomorphisms form a
subring of `Module.End R M`.  Along a formally étale scalar extension, their
unique extensions assemble into a ring homomorphism.  Composing that ring hom
with the target subring inclusion gives the corresponding action on the
base-changed module.

Before passing to endomorphisms, compatible scalar extensions of arbitrary
bounded differential operators commute with composition and add order bounds.
That more general statement is owned by
`LinearMap.IsDifferentialOperatorOfOrder.BaseChange.IsExtension.comp`.

The shared API exposes the mathematically primary subring and unique ring-hom
property. A `DifferentialOperator.FiniteOrderEndomorphisms.BaseChange.Extension`
bundles a ring hom with that property. Its `toEnd` map is the directly usable
action by ordinary endomorphisms, while `module` supplies the corresponding
module structure only when a caller explicitly needs a typeclass instance.

@stack 0H95
-/

@[stacks 0H95 "finite-order differential operators under formally etale base change"]
#check @LinearMap.IsDifferentialOperatorOfOrder.BaseChange.IsExtension.comp

#check @DifferentialOperator.finiteOrderEndomorphisms

#check @DifferentialOperator.FiniteOrderEndomorphisms.smulRingHom
#check @DifferentialOperator.FiniteOrderEndomorphisms.BaseChange.IsExtension
#check @DifferentialOperator.FiniteOrderEndomorphisms.BaseChange.IsExtensionMap
#check @DifferentialOperator.FiniteOrderEndomorphisms.BaseChange.Extension
#check @DifferentialOperator.FiniteOrderEndomorphisms.BaseChange.Extension.toEnd
#check @DifferentialOperator.FiniteOrderEndomorphisms.BaseChange.module
#check @DifferentialOperator.FiniteOrderEndomorphisms.FormallyEtale.existsUnique_extension
#check @DifferentialOperator.FiniteOrderEndomorphisms.FormallyEtale.existsUnique_extension_of_mem
#check @DifferentialOperator.FiniteOrderEndomorphisms.FormallyEtale.existsUnique_ringHom
#check @DifferentialOperator.FiniteOrderEndomorphisms.FormallyEtale.ringHom_apply_smul
