/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FourierMukai

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- Lemma 57.8.9 (1): perfect kernels between proper flat schemes over a Noetherian
base define Fourier--Mukai functors on perfect complexes. -/
@[stacks 0FYY] #check
  (AlgebraicGeometry.Scheme.FourierMukai.perfectNoetherian :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g] [Flat g]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace),
    @RingedSpace.ModuleDerived.Perfect X.toRingedSpace ⥤
      @RingedSpace.ModuleDerived.Perfect Y.toRingedSpace)

#check
  (AlgebraicGeometry.Scheme.FourierMukai.perfectNoetherian_comp_inclusionIso :
    ∀ {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g] [Flat g]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace),
    perfectNoetherian f g K ⋙ RingedSpace.ModuleDerived.Perfect.ι ≅
      RingedSpace.ModuleDerived.Perfect.ι ⋙ functor f g K.obj)

end AlgebraicGeometry.Scheme.FourierMukai
