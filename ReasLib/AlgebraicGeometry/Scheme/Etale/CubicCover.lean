/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Data.Complex.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenFiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RamificationIndex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Punctured cubic covers of complex curves

A cubic cover with a single simple ramification point yields an étale surjection
that admits no pointed refinement by open immersions and finite étale morphisms.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- A degree-three finite cover of a smooth connected affine complex curve whose distinguished
fiber consists of an unramified point and a ramified point of index two, with no ramification
away from the latter point. -/
structure CubicEtaleCover where
  /-- The base curve. -/
  X : SchemeOverField ℂ
  /-- The total curve. -/
  Y : SchemeOverField ℂ
  /-- The finite morphism from the total curve to the base. -/
  g : Y.left ⟶ X.left
  /-- The distinguished point of the base. -/
  x : X.left
  /-- The unramified point of the distinguished fiber. -/
  u : Y.left
  /-- The ramified point of the distinguished fiber. -/
  y : Y.left
  /-- The finite morphism commutes with the structure morphisms over the complex numbers. -/
  overBase : g ≫ X.hom = Y.hom
  /-- The base is affine. -/
  isAffine_X : IsAffine X.left
  /-- The base is a curve over the complex numbers. -/
  curve_X : Curve X
  /-- The total space is a curve over the complex numbers. -/
  curve_Y : Curve Y
  /-- The base is smooth over the complex numbers. -/
  smooth_X : Smooth X.hom
  /-- The total space is smooth over the complex numbers. -/
  smooth_Y : Smooth Y.hom
  /-- The cover morphism is finite. -/
  isFinite_g : IsFinite g
  /-- The cover morphism is dominant. -/
  isDominant_g : IsDominant g
  /-- The induced extension of function fields is finite. -/
  finiteFunctionFieldExtension_g :
    @FiniteFunctionFieldExtension _ _ g curve_Y.toIsIntegral curve_X.toIsIntegral isDominant_g
  /-- The cover has function-field degree three. -/
  inducedFunctionFieldDegree_eq_three :
    @inducedFunctionFieldDegree _ _ g curve_Y.toIsIntegral curve_X.toIsIntegral isDominant_g = 3
  /-- The two points of the distinguished fiber are distinct. -/
  u_ne_y : u ≠ y
  /-- The point-set fiber over the distinguished base point consists of the two given points. -/
  fiber_eq : g ⁻¹' {x} = {u, y}
  /-- The cover is unramified at the distinguished unramified point. -/
  unramifiedAt_u : g.UnramifiedAt u
  /-- The cover is ramified at the distinguished ramified point. -/
  not_unramifiedAt_y : ¬ g.UnramifiedAt y
  /-- The ramification index at the ramified point is two. -/
  ramificationIndexAt_y : g.ramificationIndexAt y = 2
  /-- The cover is unramified away from the distinguished ramified point. -/
  unramifiedAwayFrom_y : ∀ point : Y.left, point ≠ y → g.UnramifiedAt point
  /-- The ramified point is closed. -/
  y_mem_closedPoints : y ∈ closedPoints Y.left

namespace CubicEtaleCover

/-- A cubic cover has affine smooth connected base, smooth connected total curve, degree three,
and a distinguished two-point fiber with the specified unique ramification point. -/
theorem spec (c : CubicEtaleCover) :
    IsAffine c.X.left ∧ Curve c.X ∧ Curve c.Y ∧ Smooth c.X.hom ∧ Smooth c.Y.hom ∧
      IsFinite c.g ∧ IsDominant c.g ∧
      @FiniteFunctionFieldExtension _ _ c.g
        c.curve_Y.toIsIntegral c.curve_X.toIsIntegral c.isDominant_g ∧
      @inducedFunctionFieldDegree _ _ c.g
        c.curve_Y.toIsIntegral c.curve_X.toIsIntegral c.isDominant_g = 3 ∧
      c.u ≠ c.y ∧ c.g ⁻¹' {c.x} = {c.u, c.y} ∧
      c.g.UnramifiedAt c.u ∧ ¬ c.g.UnramifiedAt c.y ∧
      c.g.ramificationIndexAt c.y = 2 ∧
      (∀ point : c.Y.left, point ≠ c.y → c.g.UnramifiedAt point) ∧
      c.y ∈ closedPoints c.Y.left ∧ ConnectedSpace c.X.left ∧ ConnectedSpace c.Y.left := by
  refine ⟨c.isAffine_X, c.curve_X, c.curve_Y, c.smooth_X, c.smooth_Y,
    c.isFinite_g, c.isDominant_g, c.finiteFunctionFieldExtension_g,
    c.inducedFunctionFieldDegree_eq_three, c.u_ne_y, c.fiber_eq,
    c.unramifiedAt_u, c.not_unramifiedAt_y, c.ramificationIndexAt_y,
    c.unramifiedAwayFrom_y, c.y_mem_closedPoints, ?_, ?_⟩
  · letI : IsIntegral c.X.left := c.curve_X.toIsIntegral
    infer_instance
  · letI : IsIntegral c.Y.left := c.curve_Y.toIsIntegral
    infer_instance

/-- The open complement of the ramified point in the total curve of a cubic cover. -/
def U (c : CubicEtaleCover) : c.Y.left.Opens :=
  ⟨{c.y}ᶜ, c.y_mem_closedPoints.isOpen_compl⟩

/-- The underlying set of the punctured curve is the complement of the ramified singleton. -/
theorem coe_U (c : CubicEtaleCover) :
    (c.U : Set c.Y.left) = {c.y}ᶜ := rfl

/-- The unramified point of the distinguished fiber lies in the punctured curve. -/
theorem mem_U (c : CubicEtaleCover) : c.u ∈ c.U := by
  change c.u ∈ (c.U : Set c.Y.left)
  rw [coe_U]
  simpa using c.u_ne_y

/-- The restriction of a cubic cover to the complement of its ramified point. -/
def f (c : CubicEtaleCover) : c.U.toScheme ⟶ c.X.left :=
  c.U.ι ≫ c.g

/-- The restricted cover is the open-subscheme inclusion followed by the cover morphism. -/
theorem f_comp (c : CubicEtaleCover) : c.f = c.U.ι ≫ c.g := rfl

/-- The restriction of a cubic cover away from its ramified point is étale. -/
@[instance]
theorem etale_f (c : CubicEtaleCover) : Etale c.f := sorry

/-- The restriction of a cubic cover away from its ramified point is surjective. -/
@[instance]
theorem surjective_f (c : CubicEtaleCover) : Surjective c.f := by
  letI : IsFinite c.g := c.isFinite_g
  letI : IsDominant c.g := c.isDominant_g
  have hg : Surjective c.g := inferInstance
  have hgu : c.g c.u = c.x := by
    have hmem : c.u ∈ c.g ⁻¹' ({c.x} : Set c.X.left) := by
      rw [c.fiber_eq]
      simp
    simpa using hmem
  have hgy : c.g c.y = c.x := by
    have hmem : c.y ∈ c.g ⁻¹' ({c.x} : Set c.X.left) := by
      rw [c.fiber_eq]
      simp
    simpa using hmem
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨q, hq⟩ := hg.surj z
  by_cases hqy : q = c.y
  · subst q
    have hz : z = c.x := by
      rw [← hq, hgy]
    refine ⟨⟨c.u, c.mem_U⟩, ?_⟩
    change c.g c.u = z
    rw [hgu, hz]
  · have hqU : q ∈ c.U := by
      change q ∈ (c.U : Set c.Y.left)
      rw [coe_U]
      simpa using hqy
    refine ⟨⟨q, hqU⟩, ?_⟩
    change c.g q = z
    exact hq

/-- A point of the punctured curve lies over the distinguished base point exactly when its
image in the total curve is the distinguished unramified point. -/
theorem fiber_f (c : CubicEtaleCover) (point : c.U.toScheme) :
    c.f point = c.x ↔ c.U.ι point = c.u := by
  have hpoint_mem : c.U.ι point ∈ c.U := by
    simpa only [Scheme.Opens.ι_apply] using point.property
  constructor
  · intro hp
    have hmem : c.U.ι point ∈ c.g ⁻¹' ({c.x} : Set c.X.left) := by
      change c.g (c.U.ι point) ∈ ({c.x} : Set c.X.left)
      simpa [f] using hp
    rw [c.fiber_eq] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hmem | hmem
    · exact hmem
    · exfalso
      have hnot : c.U.ι point ∉ ({c.y} : Set c.Y.left) := by
        change c.U.ι point ∈ (c.U : Set c.Y.left) at hpoint_mem
        rw [coe_U] at hpoint_mem
        exact hpoint_mem
      exact hnot (by simpa [hmem])
  · intro hp
    have hu : c.g c.u = c.x := by
      have hmem : c.u ∈ c.g ⁻¹' ({c.x} : Set c.X.left) := by
        rw [c.fiber_eq]
        simp
      simpa using hmem
    simpa [f, hp, hu]

/-- A pointed refinement is a finite composite of open immersions and finite étale morphisms
to the base with a commuting lift to the punctured curve and a point mapping to its
distinguished unramified point. -/
def HasPointedRefinement (c : CubicEtaleCover) : Prop :=
  ∃ (W : Scheme.{0}) (h : W ⟶ c.X.left) (lift : W ⟶ c.U.toScheme) (point : W),
    openImmersionOrFiniteEtale.multiplicativeClosure h ∧
      lift ≫ c.f = h ∧ c.U.ι (lift point) = c.u

/-- Pointed refinement is equivalent to the existence of a morphism in the multiplicative
closure, a commuting lift, and a point mapping to the distinguished unramified point. -/
theorem hasPointedRefinement_iff (c : CubicEtaleCover) :
    c.HasPointedRefinement ↔
      ∃ (W : Scheme.{0}) (h : W ⟶ c.X.left) (lift : W ⟶ c.U.toScheme) (point : W),
        openImmersionOrFiniteEtale.multiplicativeClosure h ∧
          lift ≫ c.f = h ∧ c.U.ι (lift point) = c.u := by
  rfl

/-- The punctured cubic cover has no pointed refinement by a finite composite of open
immersions and finite étale morphisms. -/
theorem not_exists_pointedRefinement (c : CubicEtaleCover) :
    ¬ c.HasPointedRefinement := sorry

/-- Pointed refinement is equivalent to a descending finite tower of open immersions or
finite étale morphisms, with its first scheme isomorphic to the base, whose composite lifts
to the punctured curve and whose last scheme has a point mapping to the unramified point. -/
theorem hasPointedRefinement_iff_exists_tower (c : CubicEtaleCover) :
    c.HasPointedRefinement ↔
      ∃ (n : ℕ) (W : Fin (n + 1) → Scheme.{0})
        (step : ∀ index : Fin n, W index.succ ⟶ W index.castSucc)
        (e : W 0 ≅ c.X.left) (lift : W (Fin.last n) ⟶ c.U.toScheme)
        (point : W (Fin.last n)),
          (∀ index, openImmersionOrFiniteEtale (step index)) ∧
            Scheme.Hom.towerComposite step ≫ e.hom = lift ≫ c.f ∧
            c.U.ι (lift point) = c.u := by
  have tower_mem : ∀ (n : ℕ) (W : Fin (n + 1) → Scheme.{0})
      (step : ∀ index : Fin n, W index.succ ⟶ W index.castSucc)
      (e : W 0 ≅ c.X.left),
      (∀ index, openImmersionOrFiniteEtale (step index)) →
      openImmersionOrFiniteEtale.multiplicativeClosure
        (Scheme.Hom.towerComposite step ≫ e.hom) := by
    intro n W step e hstep
    let P : ∀ (j : Fin (n + 1)), W j ⟶ W 0 :=
      fun j => Fin.induction (motive := fun index => W index ⟶ W 0)
        (𝟙 (W 0)) (fun index composite => step index ≫ composite) j
    have haux : ∀ j : Fin (n + 1),
        openImmersionOrFiniteEtale.multiplicativeClosure (P j ≫ e.hom) := by
      apply Fin.induction (motive := fun j =>
        openImmersionOrFiniteEtale.multiplicativeClosure (P j ≫ e.hom))
      · dsimp [P]
        have he : openImmersionOrFiniteEtale e.hom := by
          rw [openImmersionOrFiniteEtale_iff]
          exact Or.inl inferInstance
        exact MorphismProperty.le_multiplicativeClosure _ _ he
      · intro index hcomp
        dsimp [P]
        have hs : openImmersionOrFiniteEtale.multiplicativeClosure (step index) :=
          MorphismProperty.le_multiplicativeClosure _ _ (hstep index)
        simpa only [Category.assoc] using
          MorphismProperty.comp_mem _ _ _ hs hcomp
    simpa [P, Scheme.Hom.towerComposite] using haux (Fin.last n)
  constructor
  · intro h
    exact (c.not_exists_pointedRefinement h).elim
  · rintro ⟨n, W, step, e, lift, point, hstep, hcomp, hpoint⟩
    have hclosure : openImmersionOrFiniteEtale.multiplicativeClosure
        (lift ≫ c.f) := by
      rw [← hcomp]
      exact tower_mem n W step e hstep
    exact ⟨W (Fin.last n), lift ≫ c.f, lift, point, hclosure, rfl, hpoint⟩

/-- No surjective finite composite of open immersions and finite étale morphisms to the base
factors through the punctured cubic cover. -/
theorem not_exists_surjective_factorization (c : CubicEtaleCover) :
    ¬ ∃ (W : Scheme.{0}) (h : W ⟶ c.X.left) (lift : W ⟶ c.U.toScheme),
        openImmersionOrFiniteEtale.multiplicativeClosure h ∧ Surjective h ∧
          lift ≫ c.f = h := by
  intro hfactor
  apply c.not_exists_pointedRefinement
  obtain ⟨W, h, lift, hclosure, hsurj, hcomm⟩ := hfactor
  obtain ⟨point, hpoint⟩ := hsurj.surj c.x
  have hfiber : c.f (lift point) = c.x := by
    calc
      c.f (lift point) = (lift ≫ c.f) point := by rfl
      _ = h point := by rw [hcomm]
      _ = c.x := hpoint
  exact ⟨W, h, lift, point, hclosure, hcomm, (c.fiber_f (lift point)).mp hfiber⟩

end CubicEtaleCover

end AlgebraicGeometry
