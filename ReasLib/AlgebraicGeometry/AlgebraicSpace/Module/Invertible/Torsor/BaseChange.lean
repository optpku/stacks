/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor

/-!
# Base change of the G_m-torsor of an invertible module

Formation of `T = Spec_X(⨁_n L^{⊗ n})` and of the tautological trivialization
`α : q^* L ≅ 𝒪_T` commutes with arbitrary base change on algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The comparison morphism `Spec_Y(⨁_n (g^* L)^{⊗ n}) ⟶ Spec_X(⨁_n L^{⊗ n})`
induced by a morphism `g : Y ⟶ X`. -/
noncomputable def gmTorsorMap {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] :
    gmTorsor ((pullback g).obj L) ⟶ gmTorsor L :=
  gmTorsorLift (gmTorsorπ ((pullback g).obj L) ≫ g) L
    ((pullbackCompIso (gmTorsorπ ((pullback g).obj L)) g).symm.app L ≪≫
      gmTorsorTriv ((pullback g).obj L))

/-- The structure morphisms identify `gmTorsorMap` with base change of `q`. -/
theorem gmTorsorMap_comp_π {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] :
    gmTorsorπ ((pullback g).obj L) ≫ g =
      gmTorsorMap g L ≫ gmTorsorπ L :=
  sorry

/-- The mediating morphism of the base-change square for `q`. -/
noncomputable def gmTorsorPullbackIso_hom {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] :
    gmTorsor ((pullback g).obj L) ⟶ Limits.pullback g (gmTorsorπ L) :=
  Limits.pullback.lift (gmTorsorπ ((pullback g).obj L)) (gmTorsorMap g L)
    (gmTorsorMap_comp_π g L)

/-- The reverse comparison of the base-change square for `q`. -/
noncomputable def gmTorsorPullbackIso_inv {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] :
    Limits.pullback g (gmTorsorπ L) ⟶ gmTorsor ((pullback g).obj L) :=
  gmTorsorLift (Limits.pullback.fst g (gmTorsorπ L)) ((pullback g).obj L)
    ((pullbackCompIso (Limits.pullback.fst g (gmTorsorπ L)) g).app L ≪≫
      eqToIso (congrArg (fun f ↦ (pullback f).obj L) (Limits.pullback.condition (f := g) (g := gmTorsorπ L))) ≪≫
      (pullbackCompIso (Limits.pullback.snd g (gmTorsorπ L)) (gmTorsorπ L)).symm.app L ≪≫
      (pullback (Limits.pullback.snd g (gmTorsorπ L))).mapIso (gmTorsorTriv L) ≪≫
      PullbackTensor.unitIso (Limits.pullback.snd g (gmTorsorπ L)))

/-- Formation of `q : T ⟶ X` commutes with base change along `g : Y ⟶ X`. -/
noncomputable def gmTorsorPullbackIso {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] :
    gmTorsor ((pullback g).obj L) ≅ Limits.pullback g (gmTorsorπ L) where
  hom := gmTorsorPullbackIso_hom g L
  inv := gmTorsorPullbackIso_inv g L
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The base-change isomorphism identifies the structure morphism of `g^* L`
with the first projection. -/
theorem gmTorsorPullbackIso_hom_fst {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] :
    (gmTorsorPullbackIso g L).hom ≫ Limits.pullback.fst g (gmTorsorπ L) =
      gmTorsorπ ((pullback g).obj L) :=
  sorry

/-- The base-change isomorphism identifies `gmTorsorMap` with the second
projection. -/
theorem gmTorsorPullbackIso_hom_snd {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] :
    (gmTorsorPullbackIso g L).hom ≫ Limits.pullback.snd g (gmTorsorπ L) =
      gmTorsorMap g L :=
  sorry

/-- Base change of the tautological trivialization `α` is compatible with
`gmTorsorMap`. Both sides are morphisms into `𝒪_T`. -/
theorem gmTorsorTriv_pullback {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] :
    (gmTorsorTriv ((pullback g).obj L)).hom =
      (pullbackCompIso (gmTorsorπ ((pullback g).obj L)) g).hom.app L ≫
        eqToHom (congrArg (fun f ↦ (pullback f).obj L) (gmTorsorMap_comp_π g L)) ≫
        (pullbackCompIso (gmTorsorMap g L) (gmTorsorπ L)).inv.app L ≫
        (pullback (gmTorsorMap g L)).map (gmTorsorTriv L).hom ≫
        (PullbackTensor.unitIso (gmTorsorMap g L)).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
