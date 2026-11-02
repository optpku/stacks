/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Hom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.DiagonalProperties
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Diagonal.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyClosed.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective.Characterization
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Equivalence.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Equivalence

/-!
# Morphism properties invariant under morphisms of thickenings of stacks

For a morphism of thickenings of algebraic stacks, each listed morphism
property holds for `f` if and only if it holds for `f'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsThickening.Hom

variable {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
variable {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
variable {f : X ⟶ Y} {f' : X' ⟶ Y'}

private theorem points_map_eq_of_iso {A B : GroupoidsOver S}
    [AlgebraicStack A] [AlgebraicStack B] {g k : A ⟶ B} (e : g ≅ k)
    (x : Points A) : Points.map g x = Points.map k x := by
  refine Quotient.inductionOn x fun p ↦ ?_
  apply Quotient.sound
  refine ⟨⟨p.map g, FieldValuedPoint.Factorization.refl (p.map g), ?_⟩⟩
  refine ⟨𝟙 _, Category.id_comp _, ?_⟩
  exact (FieldValuedPoint.Factorization.refl (p.map k)).fac_iso ≪≫
    Bicategory.whiskerLeftIso p.hom e.symm

private theorem universallyClosed_of_iso {A B : GroupoidsOver S}
    [AlgebraicStack A] [AlgebraicStack B] {g k : A ⟶ B} (e : g ≅ k)
    (hg : AlgebraicStack.UniversallyClosed g) : AlgebraicStack.UniversallyClosed k := by
  constructor
  intro Z P _ _ t fst snd iso hP
  let c := Bicategory.PseudoPullbackCone.mk k t P fst snd iso
  letI : c.IsBilimit := hP
  let el := (Bicategory.Equivalence.OnHom.id A).toEquivalence
  let er := (Bicategory.Equivalence.OnHom.id Z).toEquivalence
  let eb := (Bicategory.Equivalence.OnHom.id B).toEquivalence
  let α : (𝟙 A) ≫ g ≅ k ≫ (𝟙 B) := λ_ g ≪≫ e ≪≫ (ρ_ k).symm
  let β : (𝟙 Z) ≫ t ≅ t ≫ (𝟙 B) := λ_ t ≪≫ (ρ_ t).symm
  let ψ := Bicategory.CospanTransform.mk (𝟙 A) (𝟙 Z) (𝟙 B) α β
  let d := c.changeCospan ψ
  have hd : d.IsBilimit := Bicategory.PseudoPullbackCone.changeCospan.preserves_isBilimit
    ψ (Bicategory.CospanTransform.pointwiseEquivalenceMk el er eb α β) c
  have hc : AlgebraicStack.Closed (snd ≫ 𝟙 Z) := hg.closed_baseChange d.iso hd
  constructor
  intro U hU
  simpa only [Points.map_comp, Points.map_id] using hc.isClosedMap U hU

/-- Affine morphisms are invariant under a morphism of thickenings of algebraic
stacks. -/
theorem affine_iff (h : Hom i j f f') :
    Groupoids.Hom.Affine f ↔ Groupoids.Hom.Affine f' :=
  sorry

/-- Surjective morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem surjective_iff (h : Hom i j f f') :
    AlgebraicStack.Surjective f ↔ AlgebraicStack.Surjective f' := by
  have hw (x : Points X) :
      Points.map j (Points.map f x) = Points.map f' (Points.map i x) := by
    calc
      _ = Points.map (f ≫ j) x := (Points.map_comp f j x).symm
      _ = Points.map (i ≫ f') x := points_map_eq_of_iso h.w x
      _ = _ := Points.map_comp i f' x
  rw [AlgebraicStack.surjective_iff_map_surjective,
    AlgebraicStack.surjective_iff_map_surjective]
  constructor
  · intro hf y'
    obtain ⟨y, rfl⟩ := AlgebraicStack.Surjective.map_surjective j y'
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨Points.map i x, (hw x).symm⟩
  · intro hf' y
    obtain ⟨x', hx'⟩ := hf' (Points.map j y)
    obtain ⟨x, hx⟩ := AlgebraicStack.Surjective.map_surjective i x'
    refine ⟨x, (IsThickening.points_bijective j).1 ?_⟩
    calc
      Points.map j (Points.map f x) = Points.map f' (Points.map i x) := hw x
      _ = Points.map f' x' := congrArg (Points.map f') hx
      _ = Points.map j y := hx'

/-- Quasi-compact morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem quasiCompact_iff (h : Hom i j f f') :
    AlgebraicStack.QuasiCompact f ↔ AlgebraicStack.QuasiCompact f' := by
  constructor
  · intro hf
    letI := hf
    letI : AlgebraicStack.QuasiCompact (f ≫ j) := inferInstance
    letI : AlgebraicStack.QuasiCompact (i ≫ f') :=
      (AlgebraicStack.QuasiCompact.iso_iff h.w).mp inferInstance
    exact AlgebraicStack.QuasiCompact.of_comp_surjective i f'
  · intro hf'
    letI := hf'
    letI : AlgebraicStack.QuasiCompact (i ≫ f') := inferInstance
    letI : AlgebraicStack.QuasiCompact (f ≫ j) :=
      (AlgebraicStack.QuasiCompact.iso_iff h.w).mpr inferInstance
    exact AlgebraicStack.QuasiCompact.of_comp f j

/-- Universally closed morphisms are invariant under a morphism of thickenings
of algebraic stacks. -/
theorem universallyClosed_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyClosed f ↔ AlgebraicStack.UniversallyClosed f' := by
  have closed_immersion {A B : GroupoidsOver S} [AlgebraicStack A] [AlgebraicStack B]
      (g : A ⟶ B) [Groupoids.Hom.ClosedImmersion g] :
      AlgebraicStack.UniversallyClosed g := by
    apply (Groupoids.Hom.has_universallyClosed_iff
      (Groupoids.Hom.ClosedImmersion.representable (f := g))).mp
    intro U y Fy fy hFy
    exact ((AlgebraicSpace.IsClosedImmersion.iff_universallyClosed_locallyOfFiniteType_mono
      fy).mp (Groupoids.Hom.ClosedImmersion.of_represents y Fy fy hFy)).1
  letI : AlgebraicStack.UniversallyClosed i := closed_immersion i
  letI : AlgebraicStack.UniversallyClosed j := closed_immersion j
  constructor
  · intro hf
    letI := hf
    letI : AlgebraicStack.UniversallyClosed (i ≫ f') :=
      universallyClosed_of_iso h.w inferInstance
    exact AlgebraicStack.UniversallyClosed.of_comp_surjective i f'
  · intro hf'
    letI := hf'
    letI : AlgebraicStack.UniversallyClosed (f ≫ j) :=
      universallyClosed_of_iso h.w.symm inferInstance
    exact AlgebraicStack.UniversallyClosed.of_comp f j

/-- Integral morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem isIntegralHom_iff (h : Hom i j f f') :
    AlgebraicStack.IsIntegralHom f ↔ AlgebraicStack.IsIntegralHom f' := by
  have integral_iff {A B : GroupoidsOver S} [AlgebraicStack A] [AlgebraicStack B]
      (g : A ⟶ B) : AlgebraicStack.IsIntegralHom g ↔
        AlgebraicStack.UniversallyClosed g ∧ Groupoids.Hom.Affine g := by
    constructor
    · intro hg
      refine ⟨(Groupoids.Hom.has_universallyClosed_iff hg.representable).mp ?_,
        ⟨hg.representable, ?_⟩⟩
      · intro U y Fy fy hFy
        exact ((AlgebraicSpace.IsIntegralHom.iff_universallyClosed_and_affine fy).mp
          (hg.has_isIntegralHom y Fy fy hFy)).1
      · intro U y Fy fy hFy
        exact ((AlgebraicSpace.IsIntegralHom.iff_universallyClosed_and_affine fy).mp
          (hg.has_isIntegralHom y Fy fy hFy)).2
    · rintro ⟨hc, ha⟩
      refine ⟨ha.representable, ?_⟩
      intro U y Fy fy hFy
      exact (AlgebraicSpace.IsIntegralHom.iff_universallyClosed_and_affine fy).mpr
        ⟨(Groupoids.Hom.has_universallyClosed_iff ha.representable).mpr hc y Fy fy hFy,
          ha.of_represents y Fy fy hFy⟩
  exact (integral_iff f).trans
    ((and_congr (universallyClosed_iff h) (affine_iff h)).trans (integral_iff f').symm)

/-- Universally injective morphisms are invariant under a morphism of
thickenings of algebraic stacks. -/
theorem universallyInjective_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyInjective f ↔ AlgebraicStack.UniversallyInjective f' :=
  (AlgebraicStack.UniversallyInjective.iff_surjective_diagonal f).trans
    ((diagonal_surjective_iff h).trans
      (AlgebraicStack.UniversallyInjective.iff_surjective_diagonal f').symm)

/-- Universally open morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem universallyOpen_iff (h : Hom i j f f') :
    AlgebraicStack.UniversallyOpen f ↔ AlgebraicStack.UniversallyOpen f' :=
  sorry

/-- Quasi-DM morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem quasiDM_iff (h : Hom i j f f') :
    AlgebraicStack.QuasiDM f ↔ AlgebraicStack.QuasiDM f' := by
  constructor
  · intro hf
    exact ⟨(diagonal_locallyQuasiFinite_iff h).mp hf.locallyQuasiFinite_diagonal⟩
  · intro hf'
    exact ⟨(diagonal_locallyQuasiFinite_iff h).mpr hf'.locallyQuasiFinite_diagonal⟩

/-- DM morphisms are invariant under a morphism of thickenings of algebraic
stacks. -/
theorem dm_iff (h : Hom i j f f') :
    AlgebraicStack.DM f ↔ AlgebraicStack.DM f' := by
  constructor
  · intro hf
    exact ⟨(diagonal_unramified_iff h).mp hf.unramified_diagonal⟩
  · intro hf'
    exact ⟨(diagonal_unramified_iff h).mpr hf'.unramified_diagonal⟩

/-- Quasi-separated morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem quasiSeparated_iff (h : Hom i j f f') :
    AlgebraicStack.QuasiSeparated f ↔ AlgebraicStack.QuasiSeparated f' := by
  have hq := Groupoids.Hom.has_quasiCompact_iff
    (Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal f)
  have hq' := Groupoids.Hom.has_quasiCompact_iff
    (Groupoids.Hom.relativelyRepresentableByAlgebraicSpaces_diagonal f')
  constructor
  · intro hf
    exact ⟨hq'.mpr ((diagonal_quasiCompact_iff h).mp (hq.mp hf.quasiCompact_diagonal)),
      (diagonal_quasiSeparated_iff h).mp hf.quasiSeparated_diagonal⟩
  · intro hf'
    exact ⟨hq.mpr ((diagonal_quasiCompact_iff h).mpr (hq'.mp hf'.quasiCompact_diagonal)),
      (diagonal_quasiSeparated_iff h).mpr hf'.quasiSeparated_diagonal⟩

/-- Separated morphisms are invariant under a morphism of thickenings of
algebraic stacks. -/
theorem separated_iff (h : Hom i j f f') :
    AlgebraicStack.Separated f ↔ AlgebraicStack.Separated f' := by
  constructor
  · intro hf
    exact ⟨(diagonal_proper_iff h).mp hf.proper_diagonal⟩
  · intro hf'
    exact ⟨(diagonal_proper_iff h).mpr hf'.proper_diagonal⟩

/-- Representable morphisms, in the scheme-valued sense, are invariant under a
morphism of thickenings of algebraic stacks. -/
theorem relativelyRepresentable_iff (h : Hom i j f f') :
    FiberedCategoryOver.Groupoids.relativelyRepresentable f ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable f' :=
  sorry

/-- Morphisms representable by algebraic spaces are invariant under a morphism
of thickenings of algebraic stacks. -/
theorem relativelyRepresentableByAlgebraicSpaces_iff (h : Hom i j f f') :
    relativelyRepresentableByAlgebraicSpaces f ↔
      relativelyRepresentableByAlgebraicSpaces f' :=
  (AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_mono_diagonal f).trans
    ((diagonal_mono_iff h).trans
      (AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_mono_diagonal f').symm)

end AlgebraicGeometry.AlgebraicStack.IsThickening.Hom
