/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.SmoothStratification

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 37.55.1: near a generic point of an irreducible component of a reduced base, a
finite-presentation morphism admits, after a surjective universally injective finite locally free
base change, a finite filtration by finite-type closed subschemes whose initial stage is a
thickening and whose locally closed strata are smooth over the new base. -/
@[stacks 0H43] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_smoothStratification :
    {X S : Scheme.{u}} → (f : X ⟶ S) → [Scheme.Hom.FinitePresentation f] →
    [IsReduced S] → (η : S) → η ∈ genericPoints S →
    ∃ (U : S.Opens) (_ : η ∈ U)
      (V : Scheme.{u}) (g : V ⟶ U)
      (_ : Surjective g) (_ : UniversallyInjective g) (_ : IsFiniteLocallyFree g)
      (t : ℕ) (Z : Fin (t + 1) → (pullback f (g ≫ U.ι)).IdealSheafData)
      (_ : ∀ i : Fin (t + 1), (Z i).IsFiniteType)
      (_ : IsThickening (Z 0).subschemeι)
      (_ : ∀ i : Fin t, Z i.castSucc ≤ Z i.succ)
      (_ : Z (Fin.last t) = ⊤),
      ∀ i : Fin t,
        Smooth (Scheme.Modules.stratumMap Z i ≫ pullback.snd f (g ≫ U.ι)))
