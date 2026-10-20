/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt.ResidueExtension
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open scoped BasedFunctor

universe u

/- Lemma 98.12.5
A finite residue-field extension preserves smoothness of the predeformation
functor induced by an object versal at a finite type point, assuming the
Rim-Schlessinger condition.
-/
@[stacks 07XG] #check
  (AlgebraicGeometry.GroupoidsOver.instIsSmooth_hatResidueExtension :
    ∀ {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (l : Type u) [Field l]
    [Algebra Λ l] [Module.Finite Λ l] [Algebra (residueFieldType u0) l]
    [Module.Finite (residueFieldType u0) l]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ openImmersion =
        fromResidueExtension u0 l ≫ hU)
    [HasRimSchlessinger X] [IsVersalAt hU x hx u0],
    BasedFunctor.IsSmooth
      (hatResidueExtension hU x hx u0 l openImmersion h_factor))
