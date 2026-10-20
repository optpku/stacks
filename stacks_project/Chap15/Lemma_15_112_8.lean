module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Unramified
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.112.8

The repository path retains the legacy numbering.  The current Stacks entry is Lemma 15.113.8,
tag `0EXR`.  Its closure properties for unramified field extensions are owned by the reusable
`DVR.Field.IsUnramified` API.

@stack 0EXR
-/

/- Lemma 15.112.8 (1): unramifiedness descends in a tower of finite separable extensions. -/
@[stacks 0EXR "Lemma 15.112.8 (1): descent in a finite separable tower"]
#check @DVR.Field.IsUnramified.ofTower

/- Lemma 15.112.8 (2): an unramified finite separable extension has a finite Galois unramified
overfield. -/
@[stacks 0EXR "Lemma 15.112.8 (2): finite Galois unramified overfield"]
#check @DVR.Field.IsUnramified.existsGaloisExtension

/- Lemma 15.112.8 (3): two unramified finite separable extensions have a common finite separable
unramified overfield. -/
@[stacks 0EXR "Lemma 15.112.8 (3): common finite separable unramified extension"]
#check @DVR.Field.IsUnramified.existsCommonExtension
