/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage.Stability

/-!
# Stability of étale covering families

Étale covering families of algebraic spaces are stable under singleton
isomorphisms, indexed composition, and base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

universe u v w

#check (AlgebraicGeometry.AlgebraicSpace.Etale.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f], Etale f)

#check (AlgebraicGeometry.AlgebraicSpace.singleton_mem_etalePrecoverage_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X),
    Presieve.singleton f ∈ etalePrecoverage.coverings X ↔
      Function.Surjective (Points.map f) ∧ Etale f)

#check (AlgebraicGeometry.AlgebraicSpace.etalePrecoverage.instHasIsos :
  ∀ {S : Scheme.{u}},
    (etalePrecoverage : Precoverage (AlgebraicSpace S)).HasIsos)

#check (AlgebraicGeometry.AlgebraicSpace.etalePrecoverage.instIsStableUnderComposition :
  ∀ {S : Scheme.{u}},
    (etalePrecoverage : Precoverage (AlgebraicSpace S)).IsStableUnderComposition)

#check (AlgebraicGeometry.AlgebraicSpace.etalePrecoverage.instIsStableUnderBaseChange :
  ∀ {S : Scheme.{u}},
    (etalePrecoverage : Precoverage (AlgebraicSpace S)).IsStableUnderBaseChange)

#check
  (AlgebraicGeometry.AlgebraicSpace.etaleCovering_singleton_of_isIso :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (f : X' ⟶ X) [IsIso f],
      Presieve.ofArrows (fun _ : Unit ↦ X') (fun _ : Unit ↦ f) ∈
        etalePrecoverage.coverings X)

#check
  (AlgebraicGeometry.AlgebraicSpace.etaleCovering_comp :
    ∀ {S : Scheme.{u}} {ι : Type v} {κ : ι → Type w}
      {X : AlgebraicSpace S} {Xᵢ : ι → AlgebraicSpace S}
      (f : (i : ι) → Xᵢ i ⟶ X),
      Presieve.ofArrows Xᵢ f ∈ etalePrecoverage.coverings X →
        ∀ {Xᵢⱼ : (i : ι) → κ i → AlgebraicSpace S}
          (g : (i : ι) → (j : κ i) → Xᵢⱼ i j ⟶ Xᵢ i),
          (∀ i, Presieve.ofArrows (Xᵢⱼ i) (g i) ∈
            etalePrecoverage.coverings (Xᵢ i)) →
            Presieve.ofArrows (fun ij : Sigma κ ↦ Xᵢⱼ ij.1 ij.2)
              (fun ij : Sigma κ ↦ g ij.1 ij.2 ≫ f ij.1) ∈
                etalePrecoverage.coverings X)

#check
  (AlgebraicGeometry.AlgebraicSpace.etaleCovering_pullback :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} {ι : Type v}
      {Xᵢ : ι → AlgebraicSpace S} (f : (i : ι) → Xᵢ i ⟶ X),
      Presieve.ofArrows Xᵢ f ∈ etalePrecoverage.coverings X →
        ∀ (g : X' ⟶ X),
          Presieve.ofArrows (fun i ↦ pullback g (f i))
            (fun i ↦ pullback.fst g (f i)) ∈
              etalePrecoverage.coverings X')
