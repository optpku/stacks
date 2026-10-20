/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.PrincipalOpen.KoszulDetection
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

open RingedSpace.ModuleDerived.Koszul
open RingedSpace.OpenSubspace.Pushforward
open KoszulComplex.PowerTower
open PrincipalOpenCech

/- Lemma 36.40.1 (1): vanishing of `Ext⁽n⁾(K, E.obj)` for every `n ≥ a`, where
`K` is the affine stage-zero Koszul object associated to `f`, makes the lower truncation
at `a` of the canonical map `E.obj ⟶ Rj_*(E.obj|_U)` an isomorphism. -/
@[stacks 0GEJ] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.truncGEOpenUnit_isIso_of_extSubsingleton :
    ∀ {A : Type u} [CommRing A] {r : ℕ}
      (f : Fin r → A) (E : DerivedQCoh (Spec (CommRingCat.of A))) (a : ℤ),
      (∀ n : ℤ, a ≤ n →
        Subsingleton
          (Ext⁽n⁾(
            (affineDerivedTilde A).obj (derivedStage f 0), E.obj))) →
        IsIso
          ((t.truncGE a).map
            ((derivedAdjunction (Spec (CommRingCat.of A)).toRingedSpace
              (openSubset f)).unit.app E.obj)))

/- Lemma 36.40.1 (2): if the lower truncation at `a` of the canonical map
`E.obj ⟶ Rj_*(E.obj|_U)` is an isomorphism, then `Ext⁽n⁾(K, E.obj)` vanishes for every
`n ≥ a + 1`, where `K` is the affine stage-zero Koszul object associated to `f`. -/
@[stacks 0GEJ] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.extSubsingleton_succ_of_truncGEOpenUnit_isIso :
    ∀ {A : Type u} [CommRing A] {r : ℕ}
      (f : Fin r → A) (E : DerivedQCoh (Spec (CommRingCat.of A))) (a : ℤ),
      IsIso
          ((t.truncGE a).map
            ((derivedAdjunction (Spec (CommRingCat.of A)).toRingedSpace
              (openSubset f)).unit.app E.obj)) →
        ∀ n : ℤ, a + 1 ≤ n →
          Subsingleton
            (Ext⁽n⁾(
              (affineDerivedTilde A).obj (derivedStage f 0), E.obj)))

end AlgebraicGeometry.Scheme.DerivedQCoh
