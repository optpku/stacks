module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Flasque

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.tilde

/- Lemma 110.47.1 (1): there exists an affine scheme `X = Spec A` and an injective
`A`-module `J` such that `tilde J` is not a flasque sheaf on `X`. -/
@[stacks 0274] #check (AlgebraicGeometry.tilde.exists_injective_not_isFlasque :
    ∃ (A : CommRingCat.{u}) (J : ModuleCat.{u} A),
      Module.Injective A J ∧ ¬ TopCat.Presheaf.IsFlasque (tilde J).presheaf)

/- Lemma 110.47.1 (2): there exist an affine scheme `X = Spec A`, an injective
`A`-module `J`, and a standard open `U = PrimeSpectrum.basicOpen f` such that the
restriction `Γ(X, tilde J) ⟶ Γ(U, tilde J)` is not surjective. -/
@[stacks 0274] #check
  (AlgebraicGeometry.tilde.exists_injective_basicOpen_restriction_not_surjective :
    ∃ (A : CommRingCat.{u}) (J : ModuleCat.{u} A) (f : A),
      Module.Injective A J ∧
        ¬ Function.Surjective
            ((tilde J).presheaf.map
              (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op))

end AlgebraicGeometry.tilde
