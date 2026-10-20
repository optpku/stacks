/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FourierMukai.ExactCoherent
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Sibling

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FourierMukai

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
variable [x.FiniteType] [y.FiniteType] [IsSeparated x]
variable [IsNoetherian X]
variable [QuasiCompact (Limits.pullback.snd x y)]
variable [QuasiSeparated (Limits.pullback.snd x y)]
variable [Abelian (RingedSpace.Coh X.toRingedSpace)]
variable [Abelian (RingedSpace.Coh Y.toRingedSpace)]
variable [HasDerivedCategory.{u} (RingedSpace.Coh X.toRingedSpace)]
variable [HasDerivedCategory.{u} (RingedSpace.Coh Y.toRingedSpace)]

/-- Over a field, a base-linear exact functor between bounded coherent derived categories
of finite-type schemes with separated source that preserves the coherent heart has a sibling
represented by a coherent kernel flat over the source with support finite over the target.
For Noetherian schemes the canonical coherent comparison equivalence identifies this model
with bounded complexes of ambient modules having coherent cohomology. -/
theorem exists_sibling_coherentFourierMukai
    (F : DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
      DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace))
    [LinearOverBoundedCoh x y F] [F.CommShift ℤ] [F.IsTriangulated]
    (hF : mapsHeartToHeart F) :
    ∃ K : coherentFourierMukaiKernel x y,
      @Functor.areSiblings _ _ _ _ _ _ _ _ _ _ _
        F (boundedCoherentFunctor x y K.obj) _ _ _
        (isTriangulated_boundedCoherentFunctor x y K.obj) := sorry

end AlgebraicGeometry.Scheme.FourierMukai
