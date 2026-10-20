/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Over the spectrum of a field, every surjective pseudo-torsor is an fpqc torsor. -/
theorem ofSurjectiveOverField {k : Type u} [Field k]
    (G : Grp (Over (Spec (CommRingCat.of k))))
    (X : Mod (Over (Spec (CommRingCat.of k))) G.X)
    [Surjective X.X.hom] [Mod.IsPseudoTorsor X] : IsTorsor G X := by
  let flatCover : (Spec (CommRingCat.of k)).Cover (Scheme.precoverage (@Flat)) := by
    refine
      { I₀ := X.X.left.affineCover.I₀
        X := fun i ↦ (X.X.left.affineCover.X i)
        f := fun i ↦ X.X.left.affineCover.f i ≫ X.X.hom
        mem₀ := ?_ }
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro y
      obtain ⟨x, rfl⟩ := X.X.hom.surjective y
      refine ⟨X.X.left.affineCover.idx x, ?_⟩
      obtain ⟨z, hz⟩ := X.X.left.affineCover.covers x
      refine ⟨z, ?_⟩
      simpa [Function.comp] using congrArg X.X.hom.base hz
    · intro i
      infer_instance
  have hOpen : ∀ i, IsOpenMap (flatCover.f i) := by
    intro i
    intro U hU
    by_cases hImg : Set.Nonempty (flatCover.f i '' U)
    · rcases hImg with ⟨y₀, hy₀⟩
      have hImage : flatCover.f i '' U = Set.univ := by
        ext y
        constructor
        · intro _
          simp
        · intro _
          rcases hy₀ with ⟨x, hx, hxy₀⟩
          refine ⟨x, hx, ?_⟩
          rw [hxy₀]
          exact Subsingleton.elim _ _
      rw [hImage]
      exact isOpen_univ
    · have hImage : flatCover.f i '' U = ∅ := by
        ext y
        simp [Set.not_nonempty_iff_eq_empty.mp hImg]
      rw [hImage]
      exact isOpen_empty
  have hqc : QuasiCompactCover flatCover.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (𝒰 := flatCover) hOpen
  -- Local instance justification (proof-local temporary data): the fpqc cover constructor consumes the established quasi-compactness of this temporary flat cover by inference.
  letI : QuasiCompactCover flatCover.toPreZeroHypercover := hqc
  let fpqcCover :
      (Spec (CommRingCat.of k)).Cover Scheme.fpqcPrecoverage :=
    Scheme.Cover.ofQuasiCompactCover flatCover
  refine GroupScheme.IsTorsorFor.ofTrivializingCover
    (G := G) (X := X) inferInstance fpqcCover ?_
  intro i
  change Nonempty ((Over.mk (flatCover.f i) : Over (Spec (CommRingCat.of k))) ⟶ X.X)
  exact ⟨Over.homMk (X.X.left.affineCover.f i) rfl⟩

end AlgebraicGeometry.GroupScheme
