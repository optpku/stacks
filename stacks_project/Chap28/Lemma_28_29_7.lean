module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Invertible
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Lemma 28.29.7: for a quasi-affine scheme `X`, an invertible `𝒪_X`-module `L`, a finite
set `E`, and an open `W` containing `E`, there is a global section of `L` whose nonvanishing open
is affine, contains `E`, and is contained in `W`. -/
@[stacks 0F20] #check
  (AlgebraicGeometry.Scheme.IsQuasiAffine.exists_affineSectionNonvanishingOpen_between :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [X.IsQuasiAffine]
      {L : X.Modules} [hL : AlgebraicGeometry.Scheme.Modules.Invertible L]
      (E : Set X) (_ : E.Finite) (W : X.Opens) (_ : E ⊆ (W : Set X)),
      ∃ s : Γ(L, ⊤),
        AlgebraicGeometry.IsAffineOpen (hL.sectionNonvanishingOpen s) ∧
          E ⊆ (hL.sectionNonvanishingOpen s : Set X) ∧
            hL.sectionNonvanishingOpen s ≤ W)
