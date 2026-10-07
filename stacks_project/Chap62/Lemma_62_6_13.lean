module

public import stacks_project.Chap62.Lemma_62_6_13_System
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 62.6.13

Filtered colimit of relative cycle groups along a directed inverse limit of
Noetherian schemes with affine transitions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RelativeCycle.InverseLimit

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle.InverseLimit

/-- Lemma 62.6.13: if `S = lim_{i ∈ I} S_i` is a directed inverse limit of
Noetherian schemes with affine transition morphisms, `0 ∈ I`, and
`X_0 ⟶ S_0` is of finite type, write `X_i = S_i ×_{S_0} X_0` and
`X = S ×_{S_0} X_0`. If `S` is Noetherian too, then
`z(X/S, r) = colim_{i ≥ 0} z(X_i/S_i, r)`, where the transition maps are
`groupBaseChange` of relative `r`-cycles. -/
@[stacks 0H5D]
theorem toLimitGroup_bijective {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ j, IsNoetherian (D.obj j)] [IsNoetherian c.pt]
    [∀ {j j' : I} (h : j ≤ j'), IsAffineHom (D.map (homOfLE h))]
    (i0 : I) {X0 : Scheme.{u}} (f0 : X0 ⟶ D.obj i0) [f0.FiniteType] (r : ℕ) :
    Function.Bijective (toLimitGroup D c i0 f0 r) := sorry

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
      ∀ i, ψ.comp (leg D c i0 f0 r i) = φ i := sorry

end AlgebraicGeometry.RelativeCycle.InverseLimit
