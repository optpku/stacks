/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Modification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProperIsoOverOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PuncturedSpectrum

/-!
# Modifications over two-dimensional local spectra
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A modification over the spectrum of a two-dimensional Noetherian local domain
with normal punctured spectrum is proper and an isomorphism over the punctured spectrum. -/
@[stacks 0AE3]
theorem isProperIsoOverOpen_puncturedι_of_isModification
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : ringKrullDim A = 2) (hU : (PuncturedSpectrum.scheme A).isNormal)
    {X : AlgebraicSpace (Spec (.of A))} [IsIntegral X]
    (f : X ⟶ specSpace A) [IsModification f] :
    IsProperIsoOverOpen f (puncturedι A) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
