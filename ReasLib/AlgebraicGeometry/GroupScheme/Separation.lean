/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.GroupScheme

noncomputable section

/-- The relative difference morphism `(g₁, g₂) ↦ g₁⁻¹g₂` of a group scheme. -/
abbrev differenceMap {S : Scheme.{u}} (G : Grp (Over S)) : G.X ⊗ G.X ⟶ G.X :=
  lift (fst G.X G.X ≫ ι[G.X]) (snd G.X G.X) ≫ μ[G.X]

/-- The underlying morphism of `lift (𝟙 G.X) (𝟙 G.X)` is the diagonal of the
structure morphism of `G`. -/
theorem lift_id_id_left_eq_diagonal {S : Scheme.{u}} (G : Grp (Over S)) :
    (lift (𝟙 G.X) (𝟙 G.X)).left = pullback.diagonal G.X.hom := by
  rw [Over.lift_left]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, pullback.diagonal_fst, Over.id_left]
  · rw [pullback.lift_snd, pullback.diagonal_snd, Over.id_left]

/-- The unit section is the pullback of the relative difference morphism along the diagonal. -/
theorem isPullback_oneSection_differenceMap {S : Scheme.{u}} (G : Grp (Over S)) :
    IsPullback (lift (𝟙 G.X) (𝟙 G.X)) (toUnit G.X) (differenceMap G) η[G.X] := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · apply Over.OverMorphism.ext
    simpa [differenceMap, Over.comp_left, Over.lift_left, Category.assoc, comp_lift_assoc]
      using congrArg Over.Hom.left (GrpObj.left_inv (X := G.X))
  · intro s
    refine Over.homMk (s.fst.left ≫ (fst G.X G.X).left) ?_
    simpa using s.fst.w
  · intro s
    apply Over.OverMorphism.ext
    have hsnd :
        s.fst ≫ snd G.X G.X = s.fst ≫ fst G.X G.X := by
      have hmul :
          s.fst ≫ snd G.X G.X =
            lift (s.fst ≫ fst G.X G.X) (s.snd ≫ η[G.X]) ≫ μ[G.X] := by
        exact (GrpObj.lift_inv_left_eq (s.fst ≫ fst G.X G.X) (s.fst ≫ snd G.X G.X)
          (s.snd ≫ η[G.X])).mp (by
            simpa [differenceMap, Category.assoc, comp_lift_assoc] using s.condition)
      have hsnd_toUnit : s.snd = s.fst ≫ fst G.X G.X ≫ toUnit G.X := by
        apply Over.OverMorphism.ext
        simpa using s.snd.w
      calc
        s.fst ≫ snd G.X G.X =
            lift (s.fst ≫ fst G.X G.X) (s.snd ≫ η[G.X]) ≫ μ[G.X] := hmul
        _ = lift (s.fst ≫ fst G.X G.X)
              ((s.fst ≫ fst G.X G.X ≫ toUnit G.X) ≫ η[G.X]) ≫ μ[G.X] := by
          rw [hsnd_toUnit]
        _ = s.fst ≫ fst G.X G.X := by
          simp
    have hsnd_left :
        s.fst.left ≫ (snd G.X G.X).left = s.fst.left ≫ (fst G.X G.X).left := by
      simpa [Over.comp_left] using congrArg Over.Hom.left hsnd
    rw [Over.comp_left, lift_id_id_left_eq_diagonal]
    apply pullback.hom_ext
    · simp
    · simpa using hsnd_left.symm
  · intro s
    apply Over.OverMorphism.ext
    simpa using s.snd.w.symm
  · intro s m hm₁ _hm₂
    apply Over.OverMorphism.ext
    have hm₁_left :
        pullback.lift m.left m.left (by simpa using Over.w m) = s.fst.left := by
      simpa [Over.comp_left, Over.lift_left] using congrArg Over.Hom.left hm₁
    calc
      m.left = pullback.lift m.left m.left (by simpa using Over.w m) ≫
          pullback.fst G.X.hom G.X.hom := by
        exact (pullback.lift_fst _ _ _).symm
      _ = s.fst.left ≫ (fst G.X G.X).left := by
        simpa using congrArg (fun k => k ≫ pullback.fst G.X.hom G.X.hom) hm₁_left

/-- If the identity section of a group scheme is a closed immersion, then its diagonal is a
closed immersion. -/
theorem isClosedImmersion_diagonal_of_isClosedImmersion_one {S : Scheme.{u}}
    (G : Grp (Over S)) (hη : IsClosedImmersion η[G.X].left) :
    IsClosedImmersion (pullback.diagonal G.X.hom) := by
  let sq : IsPullback ((lift (𝟙 G.X) (𝟙 G.X)).left) ((toUnit G.X).left)
      (differenceMap G).left η[G.X].left :=
    (isPullback_oneSection_differenceMap G).map (Over.forget S)
  have hdiag : IsClosedImmersion ((lift (𝟙 G.X) (𝟙 G.X)).left) :=
    MorphismProperty.of_isPullback sq.flip hη
  rwa [lift_id_id_left_eq_diagonal] at hdiag

/-- If the identity section of a group scheme is quasi-compact, then its diagonal is
quasi-compact. -/
theorem quasiCompact_diagonal_of_quasiCompact_one {S : Scheme.{u}} (G : Grp (Over S))
    (hη : QuasiCompact η[G.X].left) : QuasiCompact (pullback.diagonal G.X.hom) := by
  let sq : IsPullback ((lift (𝟙 G.X) (𝟙 G.X)).left) ((toUnit G.X).left)
      (differenceMap G).left η[G.X].left :=
    (isPullback_oneSection_differenceMap G).map (Over.forget S)
  have hdiag : QuasiCompact ((lift (𝟙 G.X) (𝟙 G.X)).left) :=
    MorphismProperty.of_isPullback sq.flip hη
  rwa [lift_id_id_left_eq_diagonal] at hdiag

/-- The structure morphism of a group scheme is separated if and only if its identity section
is a closed immersion. -/
theorem isSeparated_iff_isClosedImmersion_one {S : Scheme.{u}} (G : Grp (Over S)) :
    AlgebraicGeometry.IsSeparated G.X.hom ↔ IsClosedImmersion η[G.X].left := by
  constructor
  · intro hsep
    exact @Scheme.Hom.Section.isClosedImmersion _ _ G.X.hom η[G.X].left hsep
      (by simpa using Over.w η[G.X])
  · intro hη
    exact ⟨isClosedImmersion_diagonal_of_isClosedImmersion_one G hη⟩

/-- The structure morphism of a group scheme is quasi-separated if and only if its identity
section is quasi-compact. -/
theorem quasiSeparated_iff_quasiCompact_one {S : Scheme.{u}} (G : Grp (Over S)) :
    QuasiSeparated G.X.hom ↔ QuasiCompact η[G.X].left := by
  constructor
  · intro hqs
    exact @Scheme.Hom.Section.quasiCompact _ _ G.X.hom η[G.X].left hqs
      (by simpa using Over.w η[G.X])
  · intro hη
    exact ⟨quasiCompact_diagonal_of_quasiCompact_one G hη⟩

/-- A group scheme with closed identity section has separated structure morphism. -/
instance instIsSeparatedOfIsClosedImmersionOne {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsClosedImmersion η[G].left] : AlgebraicGeometry.IsSeparated G.hom :=
  (isSeparated_iff_isClosedImmersion_one (Grp.mk G)).2 inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The underlying scheme of a group scheme over a field is separated. -/
instance instIsSeparated {k : Type u} [Field k] (G : SchemeOverField k) [GrpObj G] :
    G.left.IsSeparated := by
  have hη : IsClosedImmersion η[G].left :=
    isClosedImmersion_of_comp_eq_id (Y := Spec (.of k)) G.hom η[G].left (by simp)
  have hG : AlgebraicGeometry.IsSeparated G.hom :=
    (isSeparated_iff_isClosedImmersion_one (Grp.mk G)).2 hη
  refine ⟨?_⟩
  simpa using IsSeparated.stableUnderComposition.comp_mem G.hom
    (terminal.from (Spec (.of k))) hG inferInstance

/-- A group scheme with quasi-compact identity section has quasi-separated structure morphism. -/
instance instQuasiSeparatedOfQuasiCompactOne {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [QuasiCompact η[G].left] : QuasiSeparated G.hom :=
  (quasiSeparated_iff_quasiCompact_one (Grp.mk G)).2 inferInstance

end

end AlgebraicGeometry.GroupScheme
