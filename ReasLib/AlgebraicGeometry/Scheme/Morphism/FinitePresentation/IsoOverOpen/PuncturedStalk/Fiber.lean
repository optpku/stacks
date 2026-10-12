/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.IsoOverOpen.PuncturedStalk.FiniteFamily

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange

/-- Corresponding punctured-stalk base changes have isomorphic fibers over the residue-field
spectrum at each selected closed point. -/
theorem fiberIso
    {ι : Type u} [Finite ι] [Nonempty ι]
    (S : Scheme.{u}) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hs_pairwise : Function.Injective s)
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) [QuasiCompact U.ι]
    (X : FinitePresentationIsoOverOpen U)
    (Y : (i : ι) → FinitePresentationIsoOverOpen
      (PuncturedSpectrum.puncturedOpen (S.presheaf.stalk (s i))))
    (e : (puncturedStalkBaseChange S s hs_closed hs_pairwise U hU).obj X ≅ Y)
    (i : ι) :
    Nonempty
      (Over.mk (fiberOverSpecResidueField X.obj.hom (s i)).hom ≅
        Over.mk (pullback.snd (Y i).obj.hom (Spec.map (S.residue (s i))))) := sorry

end AlgebraicGeometry.FinitePresentationIsoOverOpen.puncturedStalkBaseChange
