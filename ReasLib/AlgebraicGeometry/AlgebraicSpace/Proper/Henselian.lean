/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SpecialFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Proper clopen subspaces over henselian pairs

Proper clopen subspaces of the special fibre of a separated finite-type
algebraic space over a henselian pair lift to proper clopen subspaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {A : Type u} [CommRing A]

/-- A proper clopen subspace of the special fibre of a separated finite-type
algebraic space over a henselian pair lifts to a clopen subspace proper over the
base. Its base change is isomorphic to the given subspace over the special fibre. -/
theorem exists_clopen_proper_lift (I : Ideal A) [HenselianRing A I]
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [Separated (SchemeRealization.toBase X)] [FiniteType (SchemeRealization.toBase X)]
    (Y : OpenSubspace (fiberOverQuotient I X)) (hY : IsClopen Y.pointsSet)
    [Proper (Y.ι ≫ pullback.snd (SchemeRealization.toBase X) (specQuotientι I))] :
    ∃ (W : OpenSubspace X)
      (e : Y.X ≅ pullback W.ι (pullback.fst (SchemeRealization.toBase X) (specQuotientι I))),
      IsClopen W.pointsSet ∧ Proper (W.ι ≫ SchemeRealization.toBase X) ∧
        e.hom ≫ pullback.snd W.ι
          (pullback.fst (SchemeRealization.toBase X) (specQuotientι I)) = Y.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
