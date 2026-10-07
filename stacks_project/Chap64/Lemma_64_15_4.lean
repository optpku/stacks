module

public import ReasLib.Algebra.Ring.CommutatorQuotient
import StacksCheckRecall

universe u v

variable {A : Type u} {Λ : Type v} [CommRing A] [Ring Λ] [Algebra A Λ]

/- Lemma 64.15.4: the map `A → Λ`, formalized as `algebraMap A Λ`, defines an
`A`-module structure on `Λ♮`. -/
@[stacks 03U8] #check
  (Ring.CommutatorQuotient.instModule : Module A (Ring.CommutatorQuotient Λ))
