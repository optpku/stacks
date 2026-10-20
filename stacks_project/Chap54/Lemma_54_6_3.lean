module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.Fiber

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

/- Lemma 54.6.3: if `X` corresponds to the family `Y` under punctured-stalk base change,
then the fiber of `X` at `s i` is isomorphic over `Spec (S.residueField (s i))` to the
fiber of `Y i` at the closed point. -/
@[stacks 0BFX] #check (AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange.fiberIso :
    ∀ {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange
      S s hs_closed hs_pairwise U hU).obj X ≅ Y)
    (i : ι),
    Nonempty
      (Over.mk (fiberOverSpecResidueField X.obj.hom (s i)).hom ≅
        Over.mk (pullback.snd (Y i).obj.hom (Spec.map (S.residue (s i))))))
