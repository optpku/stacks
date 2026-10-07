module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FlatStratification

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.54.2: a finite-presentation morphism between quasi-compact, quasi-separated schemes
admits a finite descending chain of finite-type closed subschemes, beginning with a thickening and
ending in the empty subscheme, over whose successive locally closed strata the morphism is flat. -/
@[stacks 0H3Z] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_flatStratification :
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
        Flat (pullback.snd f (Scheme.Modules.stratumMap Z i)))
