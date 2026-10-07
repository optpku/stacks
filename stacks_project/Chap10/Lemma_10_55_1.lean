module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length
import StacksCheckRecall

@[expose] public section

/-!
# The length homomorphism on the finite-module Grothendieck group

@stack 00JD
-/

/- Lemma 10.55.1 (Tag 00JD): over an Artinian local ring, the source length map is the
`CategoryTheory.ModuleCat.K0.finiteLength` owner specialized to the finite-module
Grothendieck group.  The owner is intentionally Artinian-general; locality belongs to later
composition-series and residue-field statements. -/
@[stacks 00JD "length homomorphism"]
#check @CategoryTheory.ModuleCat.K0.finiteLength

section SourceSpecialization

universe u

variable (R : Type u) [Ring R] [IsArtinianRing R] [IsLocalRing R]

/- The book's local-Artinian hypotheses are a specialization of the Artinian owner; keeping this
check explicit documents the bridge without adding a second root-level map. -/
@[stacks 00JD "local Artinian specialization"]
#check CategoryTheory.ModuleCat.K0.finiteLength R

end SourceSpecialization

/- The generator formula is the reusable source-facing spec. -/
@[stacks 00JD "generator formula"]
#check @CategoryTheory.ModuleCat.K0.finiteLength_finiteOf

/- The unbundled form keeps ordinary finite modules from having to be repackaged manually. -/
@[stacks 00JD "unbundled generator formula"]
#check @CategoryTheory.ModuleCat.K0.finiteLength_finiteClass
