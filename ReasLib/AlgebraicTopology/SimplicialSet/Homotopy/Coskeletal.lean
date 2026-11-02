/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 01A9

# Homotopies into coskeletal simplicial sets

Two maps into an `n`-coskeletal simplicial set admit a canonical directed homotopy as soon as
their components agree in every degree strictly below `n`. The construction first defines the
cylinder map through degree `n`, then extends it across the coskeleton adjunction.

The source need not be coskeletal. This is the natural reusable strengthening of the usual
statement in which both source and target are assumed to be `n`-coskeletal.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.SimplicialObject
open scoped MonoidalCategory Simplicial

noncomputable section

universe u

namespace SSet.Homotopy

variable {V U : SSet.{u}} {n : ℕ} {f₀ f₁ : V ⟶ U}

namespace cylinder

namespace truncated

/-- The degreewise map on the truncated cylinder. In degree `n`, it uses `f₁` precisely on
the constant-one side of `Δ[1]`; in lower degrees it uses `f₀`. -/
@[stacks 01A9 "truncated coskeletal-cylinder component"]
def app {n : ℕ} (f₀ f₁ : V ⟶ U)
    (Θ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (((SSet.truncation n).obj (V ⊗ Δ[1])).obj Θ) ⟶
      (((SSet.truncation n).obj U).obj Θ) :=
  ↾fun x ↦
    if Θ.unop.1.len = n then
      if SSet.stdSimplex.asOrderHom x.2 0 = (1 : Fin 2) then
        f₁.app (op Θ.unop.1) x.1
      else
        f₀.app (op Θ.unop.1) x.1
    else
      f₀.app (op Θ.unop.1) x.1

/-- Agreement of `f₀` and `f₁` below `n` makes `cylinder.truncated.app` natural on the
`n`-truncated simplex category. -/
@[stacks 01A9 "truncated coskeletal-cylinder naturality"]
theorem app_naturality
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    {Θ₁ Θ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (φ : Θ₁ ⟶ Θ₂) :
    ((SSet.truncation n).obj (V ⊗ Δ[1])).map φ ≫
        app f₀ f₁ Θ₂ =
      app f₀ f₁ Θ₁ ≫
        ((SSet.truncation n).obj U).map φ := by
  rcases Θ₁ with ⟨⟨⟨a⟩, ha⟩⟩
  rcases Θ₂ with ⟨⟨⟨b⟩, hb⟩⟩
  let α : ⦋b⦌ ⟶ ⦋a⦌ := φ.unop.hom
  ext ⟨v, t⟩
  change (if b = n then
      if SSet.stdSimplex.asOrderHom t (α.toOrderHom 0) = 1 then
        f₁.app (op ⦋b⦌) (V.map α.op v)
      else f₀.app (op ⦋b⦌) (V.map α.op v)
    else f₀.app (op ⦋b⦌) (V.map α.op v)) =
      U.map α.op (if a = n then
        if SSet.stdSimplex.asOrderHom t 0 = 1 then f₁.app (op ⦋a⦌) v
        else f₀.app (op ⦋a⦌) v
      else f₀.app (op ⦋a⦌) v)
  have h₀ := ConcreteCategory.congr_hom (f₀.naturality α.op) v
  have h₁ := ConcreteCategory.congr_hom (f₁.naturality α.op) v
  by_cases heq : f₀.app (op ⦋b⦌) (V.map α.op v) =
      f₁.app (op ⦋b⦌) (V.map α.op v)
  · split_ifs <;> first
      | exact h₀
      | exact h₁
      | exact heq.trans h₁
      | exact heq.symm.trans h₀
  · have hna : a = n := by
      by_contra h
      apply heq
      exact h₀.trans ((congrArg (fun k => U.map α.op (k v))
        (hbelow a (lt_of_le_of_ne ha h))).trans h₁.symm)
    have hnb : b = n := by
      by_contra h
      exact heq (ConcreteCategory.congr_hom
        (hbelow b (lt_of_le_of_ne hb h)) (V.map α.op v))
    subst a
    subst b
    have hmono : Mono α := by
      by_contra h
      have hlen : (Limits.image α).len < n := by
        apply lt_of_le_of_ne (SimplexCategory.len_le_of_epi (Limits.factorThruImage α))
        intro hlen
        haveI : IsIso (Limits.factorThruImage α) :=
          (SimplexCategory.isIso_iff_of_epi _).2 hlen.symm
        apply h
        rw [← Limits.image.fac α]
        infer_instance
      apply heq
      have hmap : V.map α.op ≫ f₀.app (op ⦋n⦌) =
          V.map α.op ≫ f₁.app (op ⦋n⦌) := by
        rw [← Limits.image.fac α, op_comp, V.map_comp, Category.assoc,
          f₀.naturality, hbelow _ hlen, ← f₁.naturality, ← Category.assoc]
      exact ConcreteCategory.congr_hom hmap v
    haveI := hmono
    have hid := SimplexCategory.eq_id_of_mono α
    simp only [↓reduceIte, Nat.reduceAdd, hid, SimplexCategory.id_toOrderHom,
      OrderHom.id_coe, id_eq, Fin.isValue, op_id, CategoryTheory.Functor.map_id, id_apply]
    split_ifs <;> first | rfl | contradiction

/-- The morphism of `n`-truncated simplicial sets determined by `cylinder.truncated.app`. -/
@[stacks 01A9 "truncated coskeletal-cylinder morphism"]
def hom
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).obj (V ⊗ Δ[1]) ⟶ (SSet.truncation n).obj U where
  app Θ := app f₀ f₁ Θ
  naturality := fun {_ _} φ ↦ app_naturality hbelow φ

/-- The component of the bundled truncated cylinder map is `cylinder.truncated.app`. -/
@[simp, stacks 01A9 "truncated coskeletal-cylinder component formula"]
theorem hom_app
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (Θ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (hom hbelow).app Θ = app f₀ f₁ Θ := rfl

/-- The truncated cylinder restricts to `f₀` at the zero endpoint. -/
@[stacks 01A9 "truncated coskeletal-cylinder zero endpoint"]
theorem hom.zero
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).map (ι₀ : V ⟶ V ⊗ Δ[1]) ≫ hom hbelow =
      (SSet.truncation n).map f₀ := by
  ext Θ x
  change (if Θ.unop.1.len = n then
    if (0 : Fin 2) = 1 then f₁.app (op Θ.unop.1) x
    else f₀.app (op Θ.unop.1) x
    else f₀.app (op Θ.unop.1) x) = f₀.app (op Θ.unop.1) x
  simp

/-- The truncated cylinder restricts to `f₁` at the one endpoint. -/
@[stacks 01A9 "truncated coskeletal-cylinder one endpoint"]
theorem hom.one
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).map (ι₁ : V ⟶ V ⊗ Δ[1]) ≫ hom hbelow =
      (SSet.truncation n).map f₁ := by
  ext Θ x
  change (if Θ.unop.1.len = n then
    if (1 : Fin 2) = 1 then f₁.app (op Θ.unop.1) x
    else f₀.app (op Θ.unop.1) x
    else f₀.app (op Θ.unop.1) x) = f₁.app (op Θ.unop.1) x
  by_cases h : Θ.unop.1.len = n
  · simp [h]
  · simpa [h] using ConcreteCategory.congr_hom
      (hbelow Θ.unop.1.len (lt_of_le_of_ne Θ.unop.2 h)) x

end truncated

namespace coskeletal

/-- The cylinder map obtained by extending `cylinder.truncated.hom` into an `n`-coskeletal
target. -/
@[stacks 01A9 "coskeletal-cylinder morphism"]
noncomputable def hom [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    V ⊗ Δ[1] ⟶ U :=
  ((coskAdj n).homEquiv (V ⊗ Δ[1]) ((SSet.truncation n).obj U))
      (truncated.hom hbelow) ≫
    (U.isoCoskOfIsCoskeletal n).inv

set_option backward.isDefEq.respectTransparency false in
/-- Extending the truncated cylinder map into a coskeletal target and then truncating recovers
the original truncated cylinder map. -/
@[stacks 01A9 "coskeletal-cylinder truncation formula"]
theorem truncation_hom [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).map (hom hbelow) = truncated.hom hbelow := by
  have hε : (SSet.truncation n).map (U.isoCoskOfIsCoskeletal n).inv =
      (SimplicialObject.coskAdj n).counit.app ((SSet.truncation n).obj U) := by
    apply (cancel_epi ((SSet.truncation n).map (U.isoCoskOfIsCoskeletal n).hom)).1
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
    exact ((SimplicialObject.coskAdj n).left_triangle_components U).symm
  rw [hom, CategoryTheory.Functor.map_comp]
  dsimp only [SSet.coskAdj]
  rw [hε]
  exact ((SimplicialObject.coskAdj n).homEquiv
    (V ⊗ Δ[1]) ((SSet.truncation n).obj U)).symm_apply_apply
    (truncated.hom hbelow)

set_option backward.isDefEq.respectTransparency false in
/-- The coskeletal cylinder restricts to `f₀` at the zero endpoint. -/
@[stacks 01A9 "coskeletal-cylinder zero endpoint"]
theorem hom.zero [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (ι₀ : V ⟶ V ⊗ Δ[1]) ≫ hom hbelow = f₀ := by
  apply (cancel_mono (U.isoCoskOfIsCoskeletal n).hom).1
  change (ι₀ ≫ hom hbelow) ≫ (SimplicialObject.coskAdj n).unit.app U =
    f₀ ≫ (SimplicialObject.coskAdj n).unit.app U
  rw [← (SimplicialObject.coskAdj n).unit_naturality,
    ← (SimplicialObject.coskAdj n).unit_naturality]
  rw [(SSet.truncation n).map_comp, truncation_hom, truncated.hom.zero]

set_option backward.isDefEq.respectTransparency false in
/-- The coskeletal cylinder restricts to `f₁` at the one endpoint. -/
@[stacks 01A9 "coskeletal-cylinder one endpoint"]
theorem hom.one [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (ι₁ : V ⟶ V ⊗ Δ[1]) ≫ hom hbelow = f₁ := by
  apply (cancel_mono (U.isoCoskOfIsCoskeletal n).hom).1
  change (ι₁ ≫ hom hbelow) ≫ (SimplicialObject.coskAdj n).unit.app U =
    f₁ ≫ (SimplicialObject.coskAdj n).unit.app U
  rw [← (SimplicialObject.coskAdj n).unit_naturality,
    ← (SimplicialObject.coskAdj n).unit_naturality]
  rw [(SSet.truncation n).map_comp, truncation_hom, truncated.hom.one]

/-- The relative condition for `cylinder.coskeletal.hom` on the bottom subcomplex is vacuous. -/
@[stacks 01A9 "coskeletal-cylinder bottom-relative condition"]
theorem hom.bot [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (⊥ : V.Subcomplex).ι ▷ Δ[1] ≫ hom hbelow =
      fst (⊥ : V.Subcomplex).toSSet Δ[1] ≫
        SSet.Subcomplex.isInitialBot.to (⊥ : U.Subcomplex).toSSet ≫
          (⊥ : U.Subcomplex).ι := by
  ext Θ x
  exact False.elim x.1.2

end coskeletal

end cylinder

namespace coskeletal

/-- Lemma 14.32.2 (01A9), in its reusable directed form: maps into an `n`-coskeletal
simplicial set which agree in degrees below `n` admit a simplicial-set homotopy. -/
@[stacks 01A9 "low-degree agreement gives a homotopy into a coskeletal simplicial set"]
noncomputable def ofEqBelow [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    SSet.Homotopy f₀ f₁ where
  h := cylinder.coskeletal.hom hbelow
  h₀ := cylinder.coskeletal.hom.zero hbelow
  h₁ := cylinder.coskeletal.hom.one hbelow
  rel := cylinder.coskeletal.hom.bot hbelow

end coskeletal

end SSet.Homotopy

namespace CategoryTheory.SimplicialObject.Homotopic

variable {V U : SSet.{u}} {n : ℕ} {f₀ f₁ : V ⟶ U}

namespace coskeletal

/-- Low-degree agreement into an `n`-coskeletal simplicial set implies the zigzag relation
generated by combinatorial simplicial-object homotopies. -/
@[stacks 01A9 "coskeletal simplicial-set homotopies induce the zigzag relation"]
theorem ofEqBelow [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    CategoryTheory.SimplicialObject.Homotopic f₀ f₁ :=
  Homotopic.of_homotopy
    (SSet.Homotopy.coskeletal.ofEqBelow hbelow).toSimplicialObjectHomotopy

end coskeletal

end CategoryTheory.SimplicialObject.Homotopic
