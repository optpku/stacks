/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FourierMukai.Sibling
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 57.12.2: a base-linear exact functor preserving coherent sheaves has a sibling
Fourier–Mukai transform with coherent source-flat kernel and support finite over the target. -/
@[stacks 0G00] #check
  (AlgebraicGeometry.Scheme.FourierMukai.exists_sibling_coherentFourierMukai :
    ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
      [x.FiniteType] [y.FiniteType] [IsSeparated x] [IsNoetherian X]
      [QuasiCompact (Limits.pullback.snd x y)]
      [QuasiSeparated (Limits.pullback.snd x y)]
      [Abelian (RingedSpace.Coh X.toRingedSpace)]
      [Abelian (RingedSpace.Coh Y.toRingedSpace)]
      [HasDerivedCategory.{u} (RingedSpace.Coh X.toRingedSpace)]
      [HasDerivedCategory.{u} (RingedSpace.Coh Y.toRingedSpace)]
      (F : DerivedCategory.Bounded (RingedSpace.Coh X.toRingedSpace) ⥤
        DerivedCategory.Bounded (RingedSpace.Coh Y.toRingedSpace))
      [LinearOverBoundedCoh x y F] [F.CommShift ℤ] [F.IsTriangulated],
      FourierMukai.mapsHeartToHeart F →
        ∃ K : coherentFourierMukaiKernel x y,
          @Functor.areSiblings _ _ _ _ _ _ _ _ _ _ _
            F (FourierMukai.boundedCoherentFunctor x y K.obj) _ _ _
            (FourierMukai.isTriangulated_boundedCoherentFunctor x y K.obj))
