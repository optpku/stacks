/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Order.DirectedInverseSystem
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.RelativeCycle.Transport
public import ReasLib.Order.DirectLimit.Tail

/-!
# Relative cycle groups along a directed inverse limit

This module names the directed system of groups `z(X_i/S_i, r)` obtained by
base change of a finite type morphism `X_0 ⟶ S_0` along a directed inverse
system of Noetherian schemes, together with the cocone legs into `z(X/S, r)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle.InverseLimit

section Stage

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u})
variable (i0 : I) {X0 : Scheme.{u}} (f0 : X0 ⟶ D.obj i0)

/-- The structure morphism `X_i ⟶ S_i` of the chosen pullback
`X_i = S_i ×_{S_0} X_0`. -/
def stageHom (i : Set.Ici i0) :
    pullback f0 (D.map (homOfLE i.2)) ⟶ D.obj i.1 :=
  pullback.snd f0 (D.map (homOfLE i.2))

variable [∀ j, IsNoetherian (D.obj j)] [f0.FiniteType]

/-- The chosen stage morphism `X_i ⟶ S_i` is locally of finite type. -/
instance instLocallyOfFiniteType_stageHom (i : Set.Ici i0) :
    LocallyOfFiniteType (stageHom D i0 f0 i) :=
  inferInstanceAs
    (LocallyOfFiniteType (pullback.snd f0 (D.map (homOfLE i.2))))

/-- Nested base change of a stage morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_stageHom_pullbackSnd
    (i : Set.Ici i0) {S' : Scheme.{u}} (g : S' ⟶ D.obj i.1) :
    LocallyOfFiniteType (pullback.snd (stageHom D i0 f0 i) g) :=
  inferInstance

variable (r : ℕ)

/-- The group `z(X_i/S_i, r)` of relative `r`-cycles on the stage pullback. -/
abbrev stageGroup (i : Set.Ici i0) :=
  group (stageHom D i0 f0 i) r

/-- Functoriality of the inverse system on composites of structure maps
`S_j ⟶ S_i ⟶ S_0`. -/
theorem transition_base_comp {i j : Set.Ici i0} (hij : i ≤ j) :
    D.map (homOfLE hij) ≫ D.map (homOfLE i.2) = D.map (homOfLE j.2) := by
  rw [← D.map_comp]
  rfl

/-- The associator identifying `S_j ×_{S_i} X_i` with `X_j = S_j ×_{S_0} X_0`. -/
def assocIso {i j : Set.Ici i0} (hij : i ≤ j) :
    pullback (stageHom D i0 f0 i) (D.map (homOfLE hij)) ≅
      pullback f0 (D.map (homOfLE j.2)) :=
  pullbackLeftPullbackSndIso f0 (D.map (homOfLE i.2)) (D.map (homOfLE hij)) ≪≫
    pullback.congrHom rfl (transition_base_comp D i0 hij)

/-- The stage associator is a morphism over `S_j`. -/
theorem assocIso_hom_snd {i j : Set.Ici i0} (hij : i ≤ j) :
    (assocIso D i0 f0 hij).hom ≫ stageHom D i0 f0 j =
      pullback.snd (stageHom D i0 f0 i) (D.map (homOfLE hij)) := by
  simp [assocIso, stageHom, Category.assoc, pullback.map, pullback.lift_snd]

/-- Base change of relative `r`-cycles along `S_j ⟶ S_i`, transported to the
chosen stage `X_j`. -/
def transition {i j : Set.Ici i0} (hij : i ≤ j) :
    stageGroup D i0 f0 r i →+ stageGroup D i0 f0 r j :=
  (groupPushforward
      (pullback.snd (stageHom D i0 f0 i) (D.map (homOfLE hij)))
      (stageHom D i0 f0 j) (assocIso D i0 f0 hij).hom (assocIso_hom_snd D i0 f0 hij) r).comp
    (groupBaseChange (stageHom D i0 f0 i) (D.map (homOfLE hij)) r)

/-- The identity transition on a stage is the identity homomorphism. -/
theorem transition_id (i : Set.Ici i0) :
    transition D i0 f0 r (le_rfl : i ≤ i) = AddMonoidHom.id _ := sorry

/-- Stage transitions compose along inequalities `i ≤ j ≤ k`. -/
theorem transition_comp {i j k : Set.Ici i0} (hij : i ≤ j) (hjk : j ≤ k) :
    (transition D i0 f0 r hjk).comp (transition D i0 f0 r hij) =
      transition D i0 f0 r (hij.trans hjk) := sorry

/-- The underlying fibrewise family of a stage transition is base change
followed by transport along `assocIso`. -/
theorem transition_apply {i j : Set.Ici i0} (hij : i ≤ j)
    (α : stageGroup D i0 f0 r i) :
    (transition D i0 f0 r hij α : (stageHom D i0 f0 j).FiberCycleFamily r) =
      familyMapOfIsoOver (assocIso D i0 f0 hij).hom
        (assocIso_hom_snd D i0 f0 hij) r
        (FamilyOfCyclesOnFibres.baseChange (stageHom D i0 f0 i) (D.map (homOfLE hij)) r
          (α : (stageHom D i0 f0 i).FiberCycleFamily r)) := rfl

/-- Stage groups and base-change transitions form a directed system indexed by
`i ≥ i0`. -/
instance instDirectedSystem :
    DirectedSystem (fun i : Set.Ici i0 ↦ stageGroup D i0 f0 r i)
      (fun i j hij ↦ transition D i0 f0 r hij) where
  map_self {i} α := DFunLike.congr_fun (transition_id D i0 f0 r i) α
  map_map {k j i} hij hjk α := DFunLike.congr_fun (transition_comp D i0 f0 r hij hjk) α

end Stage

section Limit

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
variable [∀ j, IsNoetherian (D.obj j)] [IsNoetherian c.pt]
variable (i0 : I) {X0 : Scheme.{u}} (f0 : X0 ⟶ D.obj i0) [f0.FiniteType]

/-- The structure morphism `X ⟶ S` of the chosen pullback `X = S ×_{S_0} X_0`. -/
def limitHom : pullback f0 (c.π.app i0) ⟶ c.pt :=
  pullback.snd f0 (c.π.app i0)

/-- The chosen limit morphism `X ⟶ S` is locally of finite type. -/
instance instLocallyOfFiniteType_limitHom :
    LocallyOfFiniteType (limitHom D c i0 f0) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f0 (c.π.app i0)))

/-- Nested base change of a stage morphism along a limit projection remains
locally of finite type. -/
instance instLocallyOfFiniteType_legDomain (i : Set.Ici i0) :
    LocallyOfFiniteType (pullback.snd (stageHom D i0 f0 i) (c.π.app (i : I))) :=
  MorphismProperty.pullback_snd (stageHom D i0 f0 i) (c.π.app (i : I))
    (instLocallyOfFiniteType_stageHom D i0 f0 i)

variable (r : ℕ)

/-- The group `z(X/S, r)` of relative `r`-cycles on the limit pullback. -/
abbrev limitGroup :=
  group (limitHom D c i0 f0) r

/-- The cone identity `S ⟶ S_i ⟶ S_0` equals the distinguished projection
`S ⟶ S_0`. -/
theorem leg_base_comp (i : Set.Ici i0) :
    c.π.app (i : I) ≫ D.map (homOfLE i.2) = c.π.app i0 :=
  c.w (homOfLE i.2)

/-- The associator identifying `S ×_{S_i} X_i` with `X = S ×_{S_0} X_0`. -/
def legAssocIso (i : Set.Ici i0) :
    pullback (stageHom D i0 f0 i) (c.π.app (i : I)) ≅ pullback f0 (c.π.app i0) :=
  pullbackLeftPullbackSndIso f0 (D.map (homOfLE i.2)) (c.π.app (i : I)) ≪≫
    pullback.congrHom rfl (c.w (homOfLE i.2))

/-- The limit associator is a morphism over `S`. -/
theorem legAssocIso_hom_snd (i : Set.Ici i0) :
    (legAssocIso D c i0 f0 i).hom ≫ limitHom D c i0 f0 =
      pullback.snd (stageHom D i0 f0 i) (c.π.app (i : I)) := by
  set_option backward.isDefEq.respectTransparency false in
    simp [legAssocIso, limitHom, stageHom, Category.assoc, pullback.map, pullback.lift_snd]

-- Cone projections do not determine the cone during instance synthesis, so the
-- nested-pullback property certificate is supplied explicitly in the transport maps.
/-- Base change of a stage relative `r`-cycle along `S ⟶ S_i` remains relative
after transport to the chosen limit pullback. -/
theorem leg_mem (i : Set.Ici i0) (α : stageGroup D i0 f0 r i) :
    @familyMapOfIsoOver _ _ c.pt _
        (instLocallyOfFiniteType_legDomain D c i0 f0 i)
        (limitHom D c i0 f0) inferInstance
        (legAssocIso D c i0 f0 i).hom inferInstance
        (legAssocIso_hom_snd D c i0 f0 i) r
        (FamilyOfCyclesOnFibres.baseChange (stageHom D i0 f0 i) (c.π.app (i : I)) r
          (α : (stageHom D i0 f0 i).FiberCycleFamily r)) ∈
      group (limitHom D c i0 f0) r := by
  exact @groupPushforward_mem _ _ c.pt
    (pullback.snd (stageHom D i0 f0 i) (c.π.app (i : I)))
    (limitHom D c i0 f0) inferInstance
    (instLocallyOfFiniteType_legDomain D c i0 f0 i) inferInstance
    (legAssocIso D c i0 f0 i).hom inferInstance
    (legAssocIso_hom_snd D c i0 f0 i) r
    (@groupBaseChange _ (D.obj (i : I)) c.pt (stageHom D i0 f0 i)
      (c.π.app (i : I)) inferInstance inferInstance inferInstance r α)

/-- The cocone leg `z(X_i/S_i, r) → z(X/S, r)` by base change along `S ⟶ S_i`. -/
def leg (i : Set.Ici i0) :
    stageGroup D i0 f0 r i →+ limitGroup D c i0 f0 r :=
  (((@familyMapOfIsoOver _ _ c.pt _
        (instLocallyOfFiniteType_legDomain D c i0 f0 i)
        (limitHom D c i0 f0) inferInstance
        (legAssocIso D c i0 f0 i).hom inferInstance
          (legAssocIso_hom_snd D c i0 f0 i) r).comp
        (FamilyOfCyclesOnFibres.baseChange (stageHom D i0 f0 i) (c.π.app (i : I)) r)).restrict
      (group (stageHom D i0 f0 i) r)).codRestrict
    (group (limitHom D c i0 f0) r) (leg_mem D c i0 f0 r i)

/-- Cocone legs are natural with respect to stage transitions. -/
theorem leg_naturality {i j : Set.Ici i0} (hij : i ≤ j) :
    (leg D c i0 f0 r j).comp (transition D i0 f0 r hij) =
      leg D c i0 f0 r i := sorry

/-- The underlying fibrewise family of a cocone leg is base change along
`S ⟶ S_i` followed by transport along `legAssocIso`. -/
theorem leg_apply (i : Set.Ici i0) (α : stageGroup D i0 f0 r i) :
    (leg D c i0 f0 r i α : (limitHom D c i0 f0).FiberCycleFamily r) =
      @familyMapOfIsoOver _ _ c.pt _
        (instLocallyOfFiniteType_legDomain D c i0 f0 i)
        (limitHom D c i0 f0) inferInstance
        (legAssocIso D c i0 f0 i).hom inferInstance
        (legAssocIso_hom_snd D c i0 f0 i) r
        (FamilyOfCyclesOnFibres.baseChange (stageHom D i0 f0 i) (c.π.app (i : I)) r
          (α : (stageHom D i0 f0 i).FiberCycleFamily r)) := rfl

variable [Nonempty I] [IsDirected I (· ≤ ·)]
variable [∀ {j j' : I} (h : j ≤ j'), IsAffineHom (D.map (homOfLE h))]

/-- Injectivity of the colimit comparison: cycles that become equal over `S`
already agree after base change to some later stage. -/
theorem exists_eq_of_leg_eq (hc : IsLimit c) {i : Set.Ici i0}
    (α β : stageGroup D i0 f0 r i)
    (h : leg D c i0 f0 r i α = leg D c i0 f0 r i β) :
    ∃ (j : Set.Ici i0) (hij : i ≤ j),
      transition D i0 f0 r hij α = transition D i0 f0 r hij β := sorry

/-- Surjectivity of the colimit comparison: every relative `r`-cycle on `X / S`
descends from some stage `i ≥ i0`. -/
theorem exists_of_limitGroup (hc : IsLimit c) (α : limitGroup D c i0 f0 r) :
    ∃ (i : Set.Ici i0) (αi : stageGroup D i0 f0 r i),
      leg D c i0 f0 r i αi = α := sorry

/-- Canonical additive comparison from the directed colimit of the stage
groups `z(X_i/S_i, r)` into `z(X/S, r)`. -/
def toLimitGroup :
    DirectLimit (fun i : Set.Ici i0 ↦ stageGroup D i0 f0 r i)
      (fun i j hij ↦ transition D i0 f0 r hij) →+
      limitGroup D c i0 f0 r where
  toFun :=
    DirectLimit.lift (fun i j hij ↦ transition D i0 f0 r hij)
      (fun i α ↦ leg D c i0 f0 r i α)
      (fun i j hij α ↦
        (DFunLike.congr_fun (leg_naturality D c i0 f0 r hij) α).symm)
  map_zero' := DirectLimit.lift_zero (fun i ↦ leg D c i0 f0 r i) _
  map_add' := DirectLimit.lift_add (fun i ↦ leg D c i0 f0 r i) _

/-- The comparison sends a stage class to the corresponding cocone leg. -/
theorem toLimitGroup_of (i : Set.Ici i0) (α : stageGroup D i0 f0 r i) :
    toLimitGroup D c i0 f0 r ⟦⟨i, α⟩⟧ = leg D c i0 f0 r i α := rfl

end Limit

/-- For a directed inverse system of Noetherian schemes with affine transitions
and Noetherian limit, base change of a finite-type morphism from a distinguished
stage induces a bijection from the direct limit of relative `r`-cycle groups to
the relative `r`-cycle group over the limit. -/
theorem toLimitGroup_bijective {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ j, IsNoetherian (D.obj j)] [IsNoetherian c.pt]
    [∀ {j j' : I} (h : j ≤ j'), IsAffineHom (D.map (homOfLE h))]
    (i0 : I) {X0 : Scheme.{u}} (f0 : X0 ⟶ D.obj i0) [f0.FiniteType] (r : ℕ) :
    Function.Bijective (toLimitGroup D c i0 f0 r) := by
  constructor
  · intro x y h
    obtain ⟨i, α, β, rfl, rfl⟩ :=
      DirectLimit.exists_eq_mk₂ (fun i j hij ↦ transition D i0 f0 r hij) x y
    obtain ⟨j, hij, hj⟩ := exists_eq_of_leg_eq D c i0 f0 r hc α β h
    exact Quotient.sound ⟨j, hij, hij, hj⟩
  · intro α
    obtain ⟨i, αi, h⟩ := exists_of_limitGroup D c i0 f0 r hc α
    exact ⟨⟦⟨i, αi⟩⟧, h⟩

/-- Mapping-out universal property of `z(X/S, r)` as the directed colimit of
the stage groups `z(X_i/S_i, r)`. -/
theorem group_isFilteredColimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ j, IsNoetherian (D.obj j)] [IsNoetherian c.pt]
    [∀ {j j' : I} (h : j ≤ j'), IsAffineHom (D.map (homOfLE h))]
    (i0 : I) {X0 : Scheme.{u}} (f0 : X0 ⟶ D.obj i0) [f0.FiniteType] (r : ℕ)
    (Y : Type u) [AddCommGroup Y]
    (φ : ∀ i : Set.Ici i0, stageGroup D i0 f0 r i →+ Y)
    (hφ : ∀ {i j : Set.Ici i0} (hij : i ≤ j),
      (φ j).comp (transition D i0 f0 r hij) = φ i) :
    ∃! ψ : limitGroup D c i0 f0 r →+ Y,
      ∀ i, ψ.comp (leg D c i0 f0 r i) = φ i := by
  let t : DirectLimit (fun i : Set.Ici i0 ↦ stageGroup D i0 f0 r i)
      (fun i j hij ↦ transition D i0 f0 r hij) →+ Y :=
    { toFun := DirectLimit.lift (fun i j hij ↦ transition D i0 f0 r hij)
        (fun i α ↦ φ i α)
        (fun i j hij α ↦ (DFunLike.congr_fun (hφ hij) α).symm)
      map_zero' := DirectLimit.lift_zero φ _
      map_add' := DirectLimit.lift_add φ _ }
  have hbij := toLimitGroup_bijective D c hc i0 f0 r
  obtain ⟨ψ, hψ⟩ := hbij.1.surjective_comp_right (t : _ → Y)
  have hψ_apply (x) : ψ (toLimitGroup D c i0 f0 r x) = t x :=
    congrFun hψ x
  let ψ' : limitGroup D c i0 f0 r →+ Y :=
    { toFun := ψ
      map_zero' := by
        rw [← map_zero (toLimitGroup D c i0 f0 r), hψ_apply]
        exact t.map_zero
      map_add' := by
        intro a b
        obtain ⟨x, rfl⟩ := hbij.2 a
        obtain ⟨y, rfl⟩ := hbij.2 b
        rw [← (toLimitGroup D c i0 f0 r).map_add x y,
          hψ_apply, hψ_apply, hψ_apply, t.map_add] }
  have hcomp (i) : ψ'.comp (leg D c i0 f0 r i) = φ i := by
    apply AddMonoidHom.ext
    intro α
    change ψ (leg D c i0 f0 r i α) = φ i α
    rw [← toLimitGroup_of D c i0 f0 r i α]
    exact hψ_apply _
  refine ⟨ψ', hcomp, ?_⟩
  intro χ hχ
  apply AddMonoidHom.ext
  intro α
  obtain ⟨i, αi, rfl⟩ := exists_of_limitGroup D c i0 f0 r hc α
  exact (DFunLike.congr_fun (hχ i) αi).trans
    (DFunLike.congr_fun (hcomp i) αi).symm

end AlgebraicGeometry.RelativeCycle.InverseLimit
