module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Stratification

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.54.5: if `S` is quasi-compact and quasi-separated and `X` and `Y` are
finitely presented over `S`, then `S` has a finite descending stratification, beginning with a
thickening and ending in the empty closed subscheme, on whose strata formation of the
scheme-theoretic image of `f` commutes with every base change. -/
@[stacks 0H41]
#check (AlgebraicGeometry.Scheme.Hom.exists_imageBaseChangeStratification :
  ∀ {S : Scheme.{u}} (X Y : Over S) (f : X ⟶ Y)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [Scheme.Hom.FinitePresentation X.hom]
    [Scheme.Hom.FinitePresentation Y.hom],
    ∃ (t : ℕ) (Z : Fin (t + 1) → S.IdealSheafData)
      (_ : ∀ i : Fin (t + 1), (Z i).IsFiniteType)
      (_ : IsThickening (Z 0).subschemeι)
      (_ : ∀ i : Fin t, Z i.castSucc ≤ Z i.succ)
      (_ : Z (Fin.last t) = ⊤),
      ∀ i : Fin t,
        AlgebraicGeometry.Scheme.Hom.ImageCommutesWithBaseChange
          ((Over.pullback (Scheme.Modules.stratumMap Z i)).map f))
