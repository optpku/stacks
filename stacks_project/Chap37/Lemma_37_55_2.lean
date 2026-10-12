/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.SmoothStratification

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.55.2: a finite-presentation morphism between quasi-compact, quasi-separated schemes
admits a finite filtration by finite-type closed subschemes, beginning with a thickening and ending
in the empty subscheme, such that each successive stratum has a surjective finite locally free cover
over which the pulled-back source has a finite filtration with smooth successive strata. -/
@[stacks 0H44] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_smoothStratifiedCover :
    {X S : Scheme.{u}} → (f : X ⟶ S) →
    [CompactSpace X] → [QuasiSeparatedSpace X] →
    [CompactSpace S] → [QuasiSeparatedSpace S] →
    [Scheme.Hom.FinitePresentation f] →
    ∃ (t : ℕ) (Z : Fin (t + 1) → S.IdealSheafData)
      (_ : ∀ i : Fin (t + 1), (Z i).IsFiniteType)
      (_ : IsThickening (Z 0).subschemeι)
      (_ : ∀ i : Fin t, Z i.castSucc ≤ Z i.succ)
      (_ : Z (Fin.last t) = ⊤),
      ∀ i : Fin t,
        ∃ (T : Scheme.{u})
          (g : T ⟶ (Scheme.Modules.stratumOpen Z i).toScheme)
          (_ : Surjective g) (_ : IsFiniteLocallyFree g)
          (ti : ℕ)
          (W : Fin (ti + 1) →
            (pullback f (g ≫ Scheme.Modules.stratumMap Z i)).IdealSheafData)
          (_ : ∀ j : Fin (ti + 1), (W j).IsFiniteType)
          (_ : IsThickening (W 0).subschemeι)
          (_ : ∀ j : Fin ti, W j.castSucc ≤ W j.succ)
          (_ : W (Fin.last ti) = ⊤),
          ∀ j : Fin ti,
            Smooth (Scheme.Modules.stratumMap W j ≫
              pullback.snd f (g ≫ Scheme.Modules.stratumMap Z i)))
