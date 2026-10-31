/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Triangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangles of relatively pseudo-coherent derived objects

The presentationwise relative predicates inherit the shifted two-out-of-three behavior of
absolute pseudo-coherence after restriction to each polynomial presentation.

@stack 0674
-/

@[expose] public section

noncomputable section

open CategoryTheory ObjectProperty Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.DerivedCategory

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

namespace IsMPseudoCoherentRelativeTo

private theorem isMPseudoCoherent_of_iso {S : Type*} [Ring S]
    {K L : DerivedCategory (ModuleCat S)} (e : K ≅ L) {m : ℤ}
    (hK : K.IsMPseudoCoherent m) : L.IsMPseudoCoherent m := by
  obtain ⟨E, hb, hE, f, hf, hm⟩ := hK
  refine ⟨E, hb, hE, f ≫ e.hom, ?_, ?_⟩
  · intro i hi
    haveI := hf i hi
    rw [Functor.map_comp]
    infer_instance
  · haveI := hm
    rw [Functor.map_comp]
    infer_instance

/-- Shifting a relatively `m`-pseudo-coherent object translates the bound by the shift. -/
@[stacks 0674 "relative pseudo-coherence under shifts"]
theorem shift_iff (K : DModA) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherentRelativeTo R (m - n) ↔
      K.IsMPseudoCoherentRelativeTo R m := by
  constructor
  · intro hK d α hα
    let F := ModuleCat.restrictScalarsMapDerivedCategory α.toRingHom
    exact (IsMPseudoCoherent.shift_iff (F.obj K) n m).1
      (isMPseudoCoherent_of_iso ((F.commShiftIso n).app K) (hK d α hα))
  · intro hK d α hα
    let F := ModuleCat.restrictScalarsMapDerivedCategory α.toRingHom
    exact isMPseudoCoherent_of_iso ((F.commShiftIso n).app K).symm
      ((IsMPseudoCoherent.shift_iff (F.obj K) n m).2 (hK d α hα))

/-- Lemma 15.82.6 (1): the third vertex inherits the indicated relative pseudo-coherence
bound. -/
@[stacks 0674 "(1), third vertex"]
theorem obj₃ {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R m) :
    T.obj₃.IsMPseudoCoherentRelativeTo R m := by
  intro n α hα
  let F := ModuleCat.restrictScalarsMapDerivedCategory α.toRingHom
  exact IsMPseudoCoherent.obj₃ (F.mapTriangle.obj T) (F.map_distinguished T hT)
    (h₁ n α hα) (h₂ n α hα)

/-- Lemma 15.82.6 (2): the middle vertex inherits the common relative pseudo-coherence
bound. -/
@[stacks 0674 "(2), middle vertex"]
theorem obj₂ {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R m)
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₂.IsMPseudoCoherentRelativeTo R m := by
  intro n α hα
  let F := ModuleCat.restrictScalarsMapDerivedCategory α.toRingHom
  exact IsMPseudoCoherent.obj₂ (F.mapTriangle.obj T) (F.map_distinguished T hT)
    (h₁ n α hα) (h₃ n α hα)

/-- Lemma 15.82.6 (3): the first vertex inherits the shifted relative pseudo-coherence
bound. -/
@[stacks 0674 "(3), first vertex"]
theorem obj₁ {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1) := by
  intro n α hα
  let F := ModuleCat.restrictScalarsMapDerivedCategory α.toRingHom
  exact IsMPseudoCoherent.obj₁ (F.mapTriangle.obj T) (F.map_distinguished T hT)
    (h₂ n α hα) (h₃ n α hα)

/-- Relative `m`-pseudo-coherence is invariant under isomorphism. -/
@[stacks 0674 "relative m-pseudo-coherence isomorphism invariance"]
instance isClosedUnderIsomorphisms (m : ℤ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) where
  of_iso e hK n α hα :=
    isMPseudoCoherent_of_iso
      ((ModuleCat.restrictScalarsMapDerivedCategory α.toRingHom).mapIso e) (hK n α hα)

/-- For fixed `m`, relatively `m`-pseudo-coherent objects satisfy two-out-of-three for
distinguished triangles. -/
@[stacks 0674 "relative m-pseudo-coherence triangle closure"]
instance isTriangulatedClosed₂ (m : ℤ) :
    ObjectProperty.IsTriangulatedClosed₂
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) :=
  .mk' (fun T hT h₁ h₃ ↦ obj₂ T hT h₁ h₃)

end IsMPseudoCoherentRelativeTo

namespace IsPseudoCoherentRelativeTo

/-- Relative pseudo-coherence is invariant under isomorphism. -/
@[stacks 0674 "relative pseudo-coherence isomorphism invariance"]
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) where
  of_iso e hK m :=
    ObjectProperty.prop_of_iso
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) e (hK m)

/-- Relatively pseudo-coherent objects form a triangulated object property. -/
@[stacks 0674 "relative pseudo-coherence triangulated property"]
instance isTriangulated :
    ObjectProperty.IsTriangulated
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) where
  exists_zero := by
    refine ⟨0, Limits.isZero_zero _, ?_⟩
    intro m n α hα
    let F := ModuleCat.restrictScalarsMapDerivedCategory α.toRingHom
    let E : CochainComplex (ModuleCat (MvPolynomial (Fin n) R)) ℤ :=
      HomologicalComplex.zero
    have hE : E.IsTermwiseFiniteFree := by
      refine ⟨fun i ↦ ?_⟩
      change Module.Free _ (0 : ModuleCat (MvPolynomial (Fin n) R)) ∧
        Module.Finite _ (0 : ModuleCat (MvPolynomial (Fin n) R))
      haveI := ModuleCat.subsingleton_of_isZero
        (Limits.isZero_zero (ModuleCat (MvPolynomial (Fin n) R)))
      constructor <;> infer_instance
    let e : DerivedCategory.Q.obj E ≅ F.obj 0 :=
      (DerivedCategory.Q.map_isZero HomologicalComplex.isZero_zero).iso
        (F.map_isZero (Limits.isZero_zero _))
    refine ⟨E, ⟨0, 0, ?_, ?_⟩, hE, e.hom, ?_, ?_⟩
    · exact (E.isStrictlyGE_iff 0).2 (fun i hi ↦ Limits.isZero_zero _)
    · exact (E.isStrictlyLE_iff 0).2 (fun i hi ↦ Limits.isZero_zero _)
    · intro i hi
      infer_instance
    · infer_instance
  isStableUnderShiftBy n := ⟨by
    intro K hK m
    simpa using (IsMPseudoCoherentRelativeTo.shift_iff K n (m + n)).2 (hK (m + n))⟩
  ext₂' T hT h₁ h₃ :=
    ObjectProperty.le_isoClosure _ _
      (fun m ↦ IsMPseudoCoherentRelativeTo.obj₂ T hT (h₁ m) (h₃ m))

/-- Lemma 15.82.6 (4): the third vertex is relatively pseudo-coherent when the first two
vertices are. -/
@[stacks 0674 "(4), third vertex"]
theorem obj₃ (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R) :
    T.obj₃.IsPseudoCoherentRelativeTo R := by
  intro m
  exact IsMPseudoCoherentRelativeTo.obj₃ T hT (h₁ (m + 1)) (h₂ m)

/-- Lemma 15.82.6 (5): the middle vertex is relatively pseudo-coherent when the first and third
vertices are. -/
@[stacks 0674 "(5), middle vertex"]
theorem obj₂ (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₂.IsPseudoCoherentRelativeTo R := by
  intro m
  exact IsMPseudoCoherentRelativeTo.obj₂ T hT (h₁ m) (h₃ m)

/-- Lemma 15.82.6 (6): the first vertex is relatively pseudo-coherent when the middle and third
vertices are. -/
@[stacks 0674 "(6), first vertex"]
theorem obj₁ (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₁.IsPseudoCoherentRelativeTo R := by
  intro m
  simpa using IsMPseudoCoherentRelativeTo.obj₁ (m := m - 1) T hT
    (by simpa using h₂ m) (h₃ (m - 1))

end IsPseudoCoherentRelativeTo

end CategoryTheory.DerivedCategory
