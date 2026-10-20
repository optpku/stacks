/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flatness.ArtinianLocal
import StacksCheckRecall

/-!
# A flatness criterion over an Artinian local ring

@stack 051K
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsArtinianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/- Lemma 10.101.6: for an Artinian local ring `R`, a proper ideal `I`, and an `R`-module `M`,
flatness of `M` is equivalent to flatness of `M / IM` over `R / I` together with vanishing of
`Tor₁[R](R ⧸ I, M)`.  The reusable owner is
`Module.Flat.ArtinianLocal.iff_quotient_flat_and_tor_one`. -/
@[stacks 051K]
#check (Module.Flat.ArtinianLocal.iff_quotient_flat_and_tor_one (R := R) (M := M) :
  ∀ (I : Ideal R), I ≠ ⊤ →
    (Module.Flat R M ↔
      Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) ∧
        IsZero (Tor₁[R](R ⧸ I, M))))

end
