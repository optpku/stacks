module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleProperties
import StacksCheckRecall

/-!
# Finite projectivity over a Beauville--Laszlo glueing pair

The reusable owner states the criterion for an explicit ring homomorphism;
its target-side tensor product is the canonical `S ⊗[R] M` orientation.

@stack 0BP6
-/

/- Lemma 15.91.19 (0BP6): an `R`-module is finite projective if and only if
its base change to the target ring and its localization away from `f` are
finite projective. -/
@[stacks 0BP6 "Lemma 15.91.19"]
#check @LocalizedModule.Away.BeauvilleLaszlo.finiteProjective_iff_baseChange_and_localizedAway_of_glueingPair

#check @LocalizedModule.Away.BeauvilleLaszlo.flat_iff_baseChange_and_localizedAway_of_glueingPair
