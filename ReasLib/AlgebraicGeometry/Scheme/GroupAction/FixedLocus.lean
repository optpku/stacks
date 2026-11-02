/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over

/-!
# Scheme-theoretic fixed loci of group actions

Fixed loci are diagonal–graph pullbacks. A commutative action restricts to an action on each
fixed locus.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GroupAction.FixedLocus

/-- The graph of an action automorphism, with the identity as its second component. -/
def graph {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : X ⟶ X ⨯ X :=
  prod.lift (ρ g).hom (𝟙 X)

/-- The scheme-theoretic fixed locus is the pullback of the diagonal and the action graph. -/
def fixedLocus {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : Over S :=
  pullback (diag X) (graph ρ g)

/-- The first projection from the fixed locus to the scheme on which the group acts. -/
def inclusion {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : fixedLocus ρ g ⟶ X :=
  pullback.fst (diag X) (graph ρ g)

/-- The two projections of the diagonal–graph pullback to the acting scheme coincide. -/
theorem fixedLocus_fst_eq_snd {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    pullback.fst (diag X) (graph ρ g) = pullback.snd (diag X) (graph ρ g) :=
  by
    have h := congrArg (fun f => f ≫ prod.snd)
      (pullback.condition (f := diag X) (g := graph ρ g))
    simpa only [Category.assoc, diag, graph, prod.lift_snd, Category.comp_id] using h

/-- The fixed-locus projection equalizes the chosen action automorphism and the identity. -/
theorem inclusion_spec {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    inclusion ρ g ≫ (ρ g).hom = inclusion ρ g :=
  by
    have h := congrArg (fun f => f ≫ prod.fst)
      (pullback.condition (f := diag X) (g := graph ρ g))
    change pullback.fst (diag X) (graph ρ g) ≫ (ρ g).hom =
      pullback.fst (diag X) (graph ρ g)
    have h' : pullback.snd (diag X) (graph ρ g) ≫ (ρ g).hom =
        pullback.fst (diag X) (graph ρ g) := by
      simpa only [Category.assoc, diag, graph, prod.lift_fst, Category.comp_id] using h.symm
    rw [← fixedLocus_fst_eq_snd ρ g] at h'
    exact h'

/-- The fixed-locus projection has equal composites with the diagonal and the action graph. -/
theorem fixedLocus_condition {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    inclusion ρ g ≫ diag X = inclusion ρ g ≫ graph ρ g :=
  by
    change pullback.fst (diag X) (graph ρ g) ≫ diag X =
      pullback.fst (diag X) (graph ρ g) ≫ graph ρ g
    calc
      _ = pullback.snd (diag X) (graph ρ g) ≫ graph ρ g := pullback.condition
      _ = pullback.fst (diag X) (graph ρ g) ≫ graph ρ g := by
        rw [← fixedLocus_fst_eq_snd ρ g]

/-- A commuting action automorphism carries the fixed-locus projection into the same pullback. -/
private theorem residualMap_condition {S : Scheme.{u}} {G : Type u} [CommGroup G]
    {X : Over S} (ρ : G →* Aut X) (g h : G) :
    (inclusion ρ g ≫ (ρ h).hom) ≫ diag X =
      (inclusion ρ g ≫ (ρ h).hom) ≫ graph ρ g :=
  by
    have hcomm : (ρ h).hom ≫ (ρ g).hom = (ρ g).hom ≫ (ρ h).hom := by
      simpa only [map_mul, Aut.Aut_mul_def, Iso.trans_hom] using
        congrArg (fun a : Aut X => a.hom) (congrArg ρ (mul_comm g h))
    apply prod.hom_ext
    · simp only [Category.assoc, diag, graph, prod.lift_fst, Category.comp_id]
      rw [hcomm, ← Category.assoc, inclusion_spec]
    · simp only [Category.assoc, diag, graph, prod.lift_snd]

/-- The restriction of an action automorphism to a fixed locus for a commuting element. -/
def residualMap {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h : G) : fixedLocus ρ g ⟶ fixedLocus ρ g :=
  pullback.lift (inclusion ρ g ≫ (ρ h).hom) (inclusion ρ g ≫ (ρ h).hom)
    (by exact residualMap_condition ρ g h)

/-- Restricting the identity group element gives the identity on the fixed locus. -/
private theorem residualMap_one {S : Scheme.{u}} {G : Type u} [CommGroup G]
    {X : Over S} (ρ : G →* Aut X) (g : G) :
    residualMap ρ g 1 = 𝟙 (fixedLocus ρ g) :=
  by
    apply pullback.hom_ext
    · rw [residualMap, pullback.lift_fst, map_one]
      change inclusion ρ g ≫ 𝟙 X = 𝟙 _ ≫ inclusion ρ g
      simp only [Category.comp_id, Category.id_comp]
    · rw [residualMap, pullback.lift_snd, map_one]
      change pullback.fst (diag X) (graph ρ g) ≫ 𝟙 X =
        𝟙 _ ≫ pullback.snd (diag X) (graph ρ g)
      simpa only [Category.comp_id, Category.id_comp] using fixedLocus_fst_eq_snd ρ g

/-- Restricted action maps respect multiplication in the order of automorphism multiplication. -/
private theorem residualMap_mul {S : Scheme.{u}} {G : Type u} [CommGroup G]
    {X : Over S} (ρ : G →* Aut X) (g h k : G) :
    residualMap ρ g (h * k) = residualMap ρ g k ≫ residualMap ρ g h :=
  by
    dsimp only [residualMap, inclusion, fixedLocus]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, map_mul,
        Aut.Aut_mul_def, Iso.trans_hom]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst_assoc, map_mul,
        Aut.Aut_mul_def, Iso.trans_hom]

/-- An action automorphism and its inverse restrict to an automorphism of each fixed locus. -/
def residualHom {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h : G) : Aut (fixedLocus ρ g) where
  hom := residualMap ρ g h
  inv := residualMap ρ g h⁻¹
  hom_inv_id := by rw [← residualMap_mul, inv_mul_cancel, residualMap_one]
  inv_hom_id := by rw [← residualMap_mul, mul_inv_cancel, residualMap_one]

/-- The residual action of a commutative group on the fixed locus of one of its elements. -/
def residual {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : G →* Aut (fixedLocus ρ g) where
  toFun := residualHom ρ g
  map_one' := by
    apply Iso.ext
    exact residualMap_one ρ g
  map_mul' h k := by
    apply Iso.ext
    exact residualMap_mul ρ g h k

/-- The fixed-locus projection intertwines the residual action with the original action. -/
theorem residual_hom {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h : G) :
    (residual ρ g h).hom ≫ inclusion ρ g = inclusion ρ g ≫ (ρ h).hom :=
  pullback.lift_fst _ _ _

/-- The residual action sends the identity element to the identity automorphism. -/
theorem residual_one {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : residual ρ g 1 = 1 :=
  (residual ρ g).map_one

/-- The residual action preserves multiplication. -/
theorem residual_mul {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h k : G) :
    residual ρ g (h * k) = residual ρ g h * residual ρ g k :=
  (residual ρ g).map_mul h k

/-- The action morphism from the coproduct of copies of the acting scheme. -/
def action {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) : (∐ fun _ : G ↦ X) ⟶ X :=
  Limits.Sigma.desc fun g ↦ (ρ g).hom

/-- The action morphism on a summand is the automorphism indexed by that summand. -/
theorem action_ι {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    Limits.Sigma.ι (fun _ : G ↦ X) g ≫ action ρ = (ρ g).hom :=
  Limits.Sigma.ι_desc _ g

end AlgebraicGeometry.Scheme.GroupAction.FixedLocus
