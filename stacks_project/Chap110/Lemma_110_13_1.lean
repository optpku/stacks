module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Padic

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.AffineFormalAlgebraicSpace

/- Lemma 110.13.1
The category of quasi-coherent modules on a formal algebraic space need not be
abelian, even for a Noetherian affine formal algebraic space. The concrete
witness is the p-adic formal spectrum for every prime p.
-/
@[stacks 0ALG] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.not_abelian :
    ∀ (p : ℕ) [Fact p.Prime],
      ¬ Nonempty (Abelian (QCoh (GroupoidsOver.ofPresheaf
        (AffineFormalAlgebraicSpace.padicSpectrum p).obj))))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.padic_isNoetherianAffine :
  ∀ (p : ℕ) [Fact p.Prime],
    AlgebraicGeometry.IsNoetherianAffine (𝒮 := ChosenBigFppfSite.full)
      (AffineFormalAlgebraicSpace.padicSpectrum p))
