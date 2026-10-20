/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.SourceLocus

/-! # Largest étale source opens -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces that is locally of finite presentation has a
largest open source subspace on which its restriction is étale. -/
theorem exists_isLargestSourceOpen_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    ∃ W : OpenSubspace X, (Etale (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Etale (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet) :=
  sorry

/-- The largest open source subspace on which `f` is étale is stable under base
change along morphisms that are flat and locally of finite presentation. -/
theorem isLargestSourceOpen_etale_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat g] [LocallyOfFinitePresentation g]
    (W : OpenSubspace X) (hW : (Etale (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Etale (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)) :
    (Etale ((W.inverseImage (pullback.fst f g)).ι ≫ (pullback.snd f g)) ∧
      ∀ U : OpenSubspace (pullback f g), Etale (U.ι ≫ (pullback.snd f g)) →
        U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet) :=
  sorry

/-- If `W` is a largest open source subspace on which `f` is étale, then the
points of `W` are exactly the points at which `f` is étale. -/
theorem isLargestSourceOpen_etale_pointsSet {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (W : OpenSubspace X) (hW : (Etale (W.ι ≫ f) ∧
      ∀ U : OpenSubspace X, Etale (U.ι ≫ f) →
        U.pointsSet ⊆ W.pointsSet)) :
    W.pointsSet = {x | EtaleAt f x} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
