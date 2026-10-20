/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Continuous

/-!
# Morphisms between formal spectra

Continuous ring homomorphisms over a base scheme induce contravariant morphisms
of formal spectra, and every morphism between formal spectra arises uniquely
in this way.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The morphism `Spec(B ⧸ J) ⟶ Spec(A ⧸ I)` over `S` induced by an `S`-algebra
map `φ : A →+* B` with `φ(I) ⊆ J`. -/
def stageMap {A B : Type u} [CommRing A] [TopologicalSpace A] [CommRing B]
    [TopologicalSpace B] {S : Scheme.{u}} {hA : Spec (.of A) ⟶ S}
    {hB : Spec (.of B) ⟶ S} (φ : A →+* B)
    (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    {I : WeakIdealOfDefinition A} {J : WeakIdealOfDefinition B}
    (hIJ : I.ideal ≤ Ideal.comap φ J.ideal) :
    stage B hB J ⟶ stage A hA I :=
  Over.homMk
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.lift I.ideal ((Ideal.Quotient.mk J.ideal).comp φ)
        (fun a ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp (hIJ ha))))))
    sorry

/-- The underlying scheme morphism of `stageMap` is `Spec.map` of the induced
quotient homomorphism. -/
theorem stageMap_left {A B : Type u} [CommRing A] [TopologicalSpace A] [CommRing B]
    [TopologicalSpace B] {S : Scheme.{u}} {hA : Spec (.of A) ⟶ S}
    {hB : Spec (.of B) ⟶ S} (φ : A →+* B)
    (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    {I : WeakIdealOfDefinition A} {J : WeakIdealOfDefinition B}
    (hIJ : I.ideal ≤ Ideal.comap φ J.ideal) :
    (stageMap φ h_over hIJ).left =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.lift I.ideal ((Ideal.Quotient.mk J.ideal).comp φ)
          (fun a ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp (hIJ ha))))) := sorry

/-- The morphism `spf B hB ⟶ spf A hA` induced by a continuous `S`-algebra map
`φ : A →+* B`. -/
def spfMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
    {hA : Spec (.of A) ⟶ S} {hB : Spec (.of B) ⟶ S} (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spf B hB ⟶ spf A hA :=
  let I0 : WeakIdealOfDefinition A :=
    WeakIdealOfDefinition.of
      (Classical.choose
        TopologicalRing.IsWeaklyPreadmissibleRing.exists_ideal_isWeakIdealOfDefinition)
      (Classical.choose_spec
        TopologicalRing.IsWeaklyPreadmissibleRing.exists_ideal_isWeakIdealOfDefinition)
  let induced (J : WeakIdealOfDefinition B) : WeakIdealOfDefinition A :=
    WeakIdealOfDefinition.of (I0.ideal ⊓ Ideal.comap φ J.ideal)
      (TopologicalRing.Ideal.IsWeakIdealOfDefinition.inf_of_isOpen I0.isWeak
        (IsOpen.preimage hφ
          (TopologicalRing.Ideal.IsWeakIdealOfDefinition.isOpen J.isWeak)))
  colimit.desc
    (thickenings B hB ⋙ yoneda ⋙
      presheafToSheaf (Scheme.fppfTopology.over S) (Type u))
    { pt := spf A hA
      ι :=
        { app J :=
            (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
                (yoneda.map (stageMap φ h_over inf_le_right)) ≫
              spfι A hA (induced J)
          naturality := sorry } }

/-- For weak ideals `I ⊂ A` and `J ⊂ B` with `φ(I) ⊆ J`, the stage square
`Spec(B ⧸ J) ⟶ Spec(A ⧸ I)` over `spf B hB ⟶ spf A hA` commutes. -/
theorem spfMap_comm {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
    {hA : Spec (.of A) ⟶ S} {hB : Spec (.of B) ⟶ S} (φ : A →+* B)
    (hφ : Continuous φ) (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    {I : WeakIdealOfDefinition A} {J : WeakIdealOfDefinition B}
    (hIJ : I.ideal ≤ Ideal.comap φ J.ideal) :
    (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (stageMap φ h_over hIJ)) ≫
        spfι A hA I =
      spfι B hB J ≫ spfMap φ hφ h_over := sorry

/-- Every morphism between formal spectra of weakly admissible topological rings
over `S` is induced by a unique continuous ring homomorphism compatible with `S`. -/
theorem existsUnique_eq_spfMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdmissibleRing B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (f : spf B hB ⟶ spf A hA) :
    ∃! φ : A →+* B, ∃ (hφ : Continuous φ)
      (h_over : Spec.map (CommRingCat.ofHom φ) ≫ hA = hB),
      f = spfMap φ hφ h_over := sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
