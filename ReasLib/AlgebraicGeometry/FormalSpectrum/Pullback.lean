/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Morphism
public import ReasLib.Topology.Algebra.TensorProduct.Admissibility
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Formal spectra of completed tensor products

The completed tensor product of weakly admissible algebras represents the
pullback of their formal spectra, compatibly with the canonical projections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The structure morphism `Spec (Algebra.TensorProduct.Completed C A B) ⟶ S`
induced by a structure morphism of `C`. -/
def completedStructureHom {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra C A] [Algebra C B] [TopologicalSpace A] [TopologicalSpace B]
    {S : Scheme.{u}} (hC : Spec (.of C) ⟶ S) :
    Spec (.of (Algebra.TensorProduct.Completed C A B)) ⟶ S :=
  Spec.map (CommRingCat.ofHom
      (algebraMap C (Algebra.TensorProduct.Completed C A B))) ≫
    hC

/-- `completedStructureHom hC` is `Spec.map` of `algebraMap C (Completed C A B)`
composed with `hC`. -/
theorem completedStructureHom_eq {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] [Algebra C A] [Algebra C B]
    [TopologicalSpace A] [TopologicalSpace B] {S : Scheme.{u}}
    (hC : Spec (.of C) ⟶ S) :
    completedStructureHom hC =
      Spec.map (CommRingCat.ofHom
          (algebraMap C (Algebra.TensorProduct.Completed C A B))) ≫
        hC :=
  rfl

/-- The left completed-tensor inclusion is compatible with the structure
morphisms to the base scheme. -/
theorem completedStructureHom_includeLeft {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra C A] [Algebra C B] [TopologicalSpace A] [TopologicalSpace B]
    {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hC : Spec (.of C) ⟶ S)
    (hA_over : Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ hC = hA) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.Completed.includeLeft C A B)) ≫
      hA = completedStructureHom hC :=
  sorry

/-- The right completed-tensor inclusion is compatible with the structure
morphisms to the base scheme. -/
theorem completedStructureHom_includeRight {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra C A] [Algebra C B] [TopologicalSpace A] [TopologicalSpace B]
    {S : Scheme.{u}}
    (hB : Spec (.of B) ⟶ S) (hC : Spec (.of C) ⟶ S)
    (hB_over : Spec.map (CommRingCat.ofHom (algebraMap C B)) ≫ hC = hB) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.Completed.includeRight C A B)) ≫
      hB = completedStructureHom hC :=
  sorry

/-- The formal spectrum of the completed tensor product, with weak
admissibility supplied by that of its factors and continuity of the algebra maps. -/
def spfCompleted {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    [TopologicalRing.IsWeaklyAdmissibleRing B]
    [TopologicalRing.IsWeaklyAdmissibleRing C]
    [Algebra C A] [Algebra C B] {S : Scheme.{u}}
    (hC : Spec (.of C) ⟶ S)
    (hφA : Continuous (algebraMap C A)) (hφB : Continuous (algebraMap C B))
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  @spf (Algebra.TensorProduct.Completed C A B) _ _
    (Algebra.TensorProduct.Completed.isWeaklyAdmissibleRing hφA hφB)
    S (completedStructureHom hC) _

/-- The projection from the completed tensor formal spectrum to the
left factor, induced by the canonical inclusion of rings. -/
def spfCompletedFst {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    [TopologicalRing.IsWeaklyAdmissibleRing B]
    [TopologicalRing.IsWeaklyAdmissibleRing C]
    [Algebra C A] [Algebra C B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hC : Spec (.of C) ⟶ S)
    (hφA : Continuous (algebraMap C A)) (hφB : Continuous (algebraMap C B))
    (hA_over : Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ hC = hA)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spfCompleted hC hφA hφB ⟶ spf A hA :=
  @spfMap A (Algebra.TensorProduct.Completed C A B) _ _ _ _ _
    (Algebra.TensorProduct.Completed.isWeaklyAdmissibleRing hφA hφB)
    S hA (completedStructureHom hC)
    (Algebra.TensorProduct.Completed.includeLeft C A B)
    (Algebra.TensorProduct.Completed.continuous_includeLeft C A B)
    (completedStructureHom_includeLeft hA hC hA_over) _

/-- The projection from the completed tensor formal spectrum to the
right factor, induced by the canonical inclusion of rings. -/
def spfCompletedSnd {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    [TopologicalRing.IsWeaklyAdmissibleRing B]
    [TopologicalRing.IsWeaklyAdmissibleRing C]
    [Algebra C A] [Algebra C B] {S : Scheme.{u}}
    (hB : Spec (.of B) ⟶ S) (hC : Spec (.of C) ⟶ S)
    (hφA : Continuous (algebraMap C A)) (hφB : Continuous (algebraMap C B))
    (hB_over : Spec.map (CommRingCat.ofHom (algebraMap C B)) ≫ hC = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    spfCompleted hC hφA hφB ⟶ spf B hB :=
  @spfMap B (Algebra.TensorProduct.Completed C A B) _ _ _ _ _
    (Algebra.TensorProduct.Completed.isWeaklyAdmissibleRing hφA hφB)
    S hB (completedStructureHom hC)
    (Algebra.TensorProduct.Completed.includeRight C A B)
    (Algebra.TensorProduct.Completed.continuous_includeRight C A B)
    (completedStructureHom_includeRight hB hC hB_over) _

/-- The pullback of formal spectra is the formal spectrum of the completed
tensor product, with an isomorphism commuting with both canonical projections. -/
theorem pullback_spfMap_iso_spfCompleted {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    [TopologicalRing.IsWeaklyAdmissibleRing B]
    [TopologicalRing.IsWeaklyAdmissibleRing C]
    [Algebra C A] [Algebra C B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S) (hB : Spec (.of B) ⟶ S) (hC : Spec (.of C) ⟶ S)
    (hφA : Continuous (algebraMap C A)) (hφB : Continuous (algebraMap C B))
    (hA_over : Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ hC = hA)
    (hB_over : Spec.map (CommRingCat.ofHom (algebraMap C B)) ≫ hC = hB)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    [HasPullbacks (Sheaf (Scheme.fppfTopology.over S) (Type u))] :
    ∃ e : pullback (spfMap (algebraMap C A) hφA hA_over)
        (spfMap (algebraMap C B) hφB hB_over) ≅ spfCompleted hC hφA hφB,
      e.hom ≫ spfCompletedFst hA hC hφA hφB hA_over =
        pullback.fst (spfMap (algebraMap C A) hφA hA_over)
          (spfMap (algebraMap C B) hφB hB_over) ∧
      e.hom ≫ spfCompletedSnd hB hC hφA hφB hB_over =
        pullback.snd (spfMap (algebraMap C A) hφA hA_over)
          (spfMap (algebraMap C B) hφB hB_over) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
