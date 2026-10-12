/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.AtWorstNodalResolution

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 55.14.3: a quasi-compact at-worst-nodal relative-dimension-one scheme over a
discrete valuation ring with smooth generic fibre admits a finite sequence of blowups at
singular closed points, preserving at-worst-nodality at every stage and ending in a regular
scheme. -/
@[stacks 0CDE] #check (AlgebraicGeometry.Scheme.Hom.exists_regular_singularPointBlowupSequence :
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [AtWorstNodal f]
    [Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))],
    ∃ (m : ℕ) (Y : Scheme.{u})
      (s : Scheme.SingularPointBlowupSequence X Y),
      s.length = m ∧ Scheme.Regular Y ∧
        s.EveryTargetAtWorstNodal f)
