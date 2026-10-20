module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S) (E : ModuleCat.{max u v} R) [Injective E]

/- Lemma 47.3.4: if `E` is an injective `R`-module, then its coextension
`(ModuleCat.coextendScalars f).obj E`, whose carrier is `Hom_R(S, E)`, is an injective
`S`-module. -/
@[stacks 08XR] #check
  (ModuleCat.CoextendScalars.injective f E :
    Injective ((ModuleCat.coextendScalars f).obj E))
