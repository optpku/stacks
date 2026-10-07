module

public import ReasLib.RingTheory.RingHom.Fiber.PurelyInseparable
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.46.8

The base-change assertion is a reusable property of a ring homomorphism, not a
chapter-local proof package.  Its owner is
`RingHom.ResidueField.MapsPurelyInseparable.BaseChange.injective_comap`.
The chapter entry is therefore a source-labelled recall block; consumers should
import the ReasLib leaf directly.

@stack 0BRB
-/

/- Lemma 10.46.8: injectivity on spectra and purely inseparable residue-field
extensions are stable under arbitrary tensor-product base change. -/
@[stacks 0BRB "base-change injectivity on spectra"]
#check @RingHom.ResidueField.MapsPurelyInseparable.BaseChange.injective_comap

/- Fine-grained owners used by later base-change arguments. -/
@[stacks 0BRB "primewise residue-field predicate"]
#check @RingHom.ResidueField.IsPurelyInseparableAt

@[stacks 0BRB "all-primes residue-field predicate"]
#check @RingHom.ResidueField.MapsPurelyInseparable

@[stacks 0BRB "primewise projection"]
#check @RingHom.ResidueField.MapsPurelyInseparable.atPrime

@[stacks 0BRB "residue-field map from a contraction equality"]
#check @RingHom.ResidueField.MapsPurelyInseparable.map_isPurelyInseparable_of_comap_eq

@[stacks 0BRB "ring-hom base-change criterion"]
#check @RingHom.ResidueField.MapsPurelyInseparable.BaseChange.injective_comap_of_ringHoms
