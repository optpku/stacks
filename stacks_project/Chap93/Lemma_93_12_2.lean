/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FlatLift.BaseChange
import StacksCheckRecall

/-!
# Flat lifts along a nilpotent cartesian diagram
-/

@[expose] public section

open CategoryTheory.ModuleCat

universe u

/- Lemma 93.12.2: for a commutative diagram of Noetherian rings with cartesian
squares, flat horizontal arrows, and surjective vertical arrows whose kernels
are nilpotent, if `J' ⊆ P'` satisfies `P' ⧸ J' ≃ Q' ⧸ J' Q'` and every `M_g`
for `g ∈ J'` has an `A'`-flat `(P')_g`-lift, then an `A`-flat `P`-module `M`
has an `A'`-flat `P'`-lift if and only if `M ⊗[P] Q` has an `A'`-flat `Q'`-lift. -/
@[stacks 0DZ2]
#check (CategoryTheory.ModuleCat.NilpotentLift.existsFlatLift_iff_existsFlatLift_extendScalars :
    ∀ {A' A P' P Q' Q : Type u}
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing Q'] [CommRing Q]
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q']
    [Algebra A P] [Algebra P' P] [Algebra P' Q'] [Algebra P Q] [Algebra Q' Q]
    [Algebra A' P] [Algebra P' Q]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' P' Q']
    [IsScalarTower P' P Q] [IsScalarTower P' Q' Q]
    (hcartAP : CategoryTheory.IsPullback
      (CommRingCat.ofHom (algebraMap A' P')) (CommRingCat.ofHom (algebraMap A' A))
      (CommRingCat.ofHom (algebraMap P' P)) (CommRingCat.ofHom (algebraMap A P)))
    (hcartPQ : CategoryTheory.IsPullback
      (CommRingCat.ofHom (algebraMap P' Q')) (CommRingCat.ofHom (algebraMap P' P))
      (CommRingCat.ofHom (algebraMap Q' Q)) (CommRingCat.ofHom (algebraMap P Q)))
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P']
    [IsNoetherianRing P] [IsNoetherianRing Q'] [IsNoetherianRing Q]
    [Module.Flat A' P'] [Module.Flat P' Q'] [Module.Flat A P] [Module.Flat P Q]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hkerA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : IsNilpotent (RingHom.ker (algebraMap P' P)))
    (hsurjQ : Function.Surjective (algebraMap Q' Q))
    (hkerQ : IsNilpotent (RingHom.ker (algebraMap Q' Q)))
    (J' : Ideal P')
    (hJ : Function.Bijective ((algebraMap P' Q').quotientByIdeal J'))
    (M : ModuleCat.{u} P)
    (hMflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A P)).obj M))
    (hloc : ∀ g ∈ J', NilpotentLift.existsFlatLift_away A' P' g M),
    NilpotentLift.existsFlatLift A' P' M ↔
      NilpotentLift.existsFlatLift A' Q' ((ModuleCat.extendScalars (algebraMap P Q)).obj M))

end
