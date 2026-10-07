module

public import stacks_project.Chap61.Definition_61_4_1_IndZariski
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 61.4.1: a ring map `A → B` is ind-Zariski if `B` can be written as
a filtered colimit `B = colim Bᵢ` with each `A → Bᵢ` a local isomorphism, i.e.
an `Algebra.IsLocalIso` stage. Canonical owner: `RingHom.IndZariski`. -/
@[stacks 096N] #check (@RingHom.IndZariski :
  ∀ {R : Type u} {A : Type v} [CommRing R] [CommRing A], (R →+* A) → Prop)

#check RingHom.IndZariski.Raw
#check RingHom.IndZariski.ofRaw
#check RingHom.IndZariski.ofIsLocalIso
