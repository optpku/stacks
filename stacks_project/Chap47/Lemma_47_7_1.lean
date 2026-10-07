module

public import ReasLib.Algebra.Module.Injective.KernelAnnihilator
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 47.7.1: Let `f : R →+* S` be a surjective map of local rings. If `iota`
exhibits an `R`-module `E` as an injective hull of the residue field of `R`, then the
map induced by `iota` into the submodule of `E` annihilated by `RingHom.ker f` is an
injective hull of the residue field of `S` over `S`. -/
@[stacks 08Z2] #check
  (LinearMap.IsInjectiveHull.kernelAnnihilator :
    ∀ {R : Type u} {S : Type v} {E : Type w}
      [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
      [AddCommGroup E] [Module R E] [Module.Injective R E],
      (f : R →+* S) → (hf : Function.Surjective f) →
        (iota : IsLocalRing.ResidueField R →ₗ[R] E) →
          iota.IsInjectiveHull →
            (iota.toKernelAnnihilator f hf).IsInjectiveHull)
