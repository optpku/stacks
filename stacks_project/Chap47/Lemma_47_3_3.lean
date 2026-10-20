module

public import ReasLib.RingTheory.Algebra.IsEpi.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 47.3.3: If `f : R →+* S` is an epimorphism and an `S`-module `E` is injective
after restriction of scalars to `R`, then `E` is injective as an `S`-module. -/
@[stacks 08YV] #check
  (ModuleCat.RestrictScalars.injective_of_epi :
    ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
      [Epi (CommRingCat.ofHom f)] (E : ModuleCat.{v} S)
      [Injective ((ModuleCat.restrictScalars.{v} f).obj E)], Injective E)
