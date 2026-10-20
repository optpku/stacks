/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.SourceLocus

/-! # Largest locally quasi-finite source opens -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The quasi-finite locus is a largest open source subspace on which `f` is
locally quasi-finite. -/
theorem isLargestSourceOpen_locallyQuasiFinite_quasiFiniteLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    (LocallyQuasiFinite ((quasiFiniteLocus f).ι ≫ f) ∧
      ∀ U : OpenSubspace X, LocallyQuasiFinite (U.ι ≫ f) →
        U.pointsSet ⊆ (quasiFiniteLocus f).pointsSet) :=
  sorry

/-- A locally finite-type morphism of algebraic spaces has a largest open source
subspace on which its restriction is locally quasi-finite. -/
theorem exists_isLargestSourceOpen_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    ∃ W : OpenSubspace X, (LocallyQuasiFinite (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, LocallyQuasiFinite (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet) :=
  sorry

/-- The largest open source subspace on which `f` is locally quasi-finite is
stable under arbitrary base change. -/
theorem isLargestSourceOpen_locallyQuasiFinite_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] (W : OpenSubspace X)
    (hW : (LocallyQuasiFinite (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, LocallyQuasiFinite (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)) :
    (LocallyQuasiFinite ((W.inverseImage (pullback.fst f g)).ι ≫ (pullback.snd f g)) ∧
      ∀ U : OpenSubspace (pullback f g), LocallyQuasiFinite (U.ι ≫ (pullback.snd f g)) →
        U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet) :=
  sorry

/-- Under the locally-of-finite-type hypothesis, a largest source open for
locally quasi-finite morphisms is the same as a largest source open for
relative dimension at most `0`. -/
theorem isLargestSourceOpen_locallyQuasiFinite_iff_relativeDimensionLE_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (W : OpenSubspace X) :
    (LocallyQuasiFinite (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, LocallyQuasiFinite (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet) ↔
      (RelativeDimensionLE (W.ι ≫ f) 0 ∧
      ∀ U : OpenSubspace X, RelativeDimensionLE (U.ι ≫ f) 0 →
        U.pointsSet ⊆ W.pointsSet) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
