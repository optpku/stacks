/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded

@[expose] public section

open AlgebraicGeometry CategoryTheory DerivedCategory.Plus.CohomologyIn
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a proper morphism of Noetherian schemes that is an isomorphism over an open,
the tensor-duality comparison is invertible on every bounded-below quasicoherent complex
after restricting to that open inverse image. -/
theorem pullbackTensorDualityMapRestrictionIsIso
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace]
    [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (V : Y.Opens) [IsIso (f ∣_ V)] (K : DerivedQCoh.Plus Y) :
    IsIso
      ((pullback (f ⁻¹ᵁ V).ι).map
        (pullbackTensorDualityMap f a aAdjunction
          ((toUnbounded Y.toRingedSpace.quasiCoherentModuleProperty).obj K))) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
