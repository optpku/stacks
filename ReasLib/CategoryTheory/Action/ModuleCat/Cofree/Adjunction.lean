/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofree linear actions

For a ring `R` and a monoid `G`, this file constructs the cofree `R`-linear `G`-action on an
`R`-module. Its carrier is `G → M`, with `G` acting by right translation. The construction and
its forgetful/cofree adjunction are independent of injective objects and transfinite iteration.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.Action.ModuleCat

noncomputable section

namespace Cofree

variable (R : Type u) (G : Type v) [Ring R] [Monoid G]

/-- The cofree `R`-linear `G`-action on `M`, with carrier `G → M` and right translation. -/
@[stacks 04JF "cofree algebraic action"]
def obj (M : ModuleCat.{max u v} R) : Action (ModuleCat.{max u v} R) G where
  V := ModuleCat.of R (G → M)
  ρ :=
    { toFun := fun g ↦
        ModuleCat.ofHom
          { toFun := fun f h ↦ f (h * g)
            map_add' := by intros; rfl
            map_smul' := by intros; rfl }
      map_one' := by
        apply _root_.ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        funext h
        change f (h * 1) = f h
        rw [mul_one]
      map_mul' := by
        intro g h
        apply _root_.ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        funext k
        change f (k * (g * h)) = f ((k * g) * h)
        rw [mul_assoc] }

/-- A module morphism acts on cofree actions by postcomposition. -/
def map {M N : ModuleCat.{max u v} R} (f : M ⟶ N) : obj R G M ⟶ obj R G N where
  hom :=
    ModuleCat.ofHom
      { toFun := fun x g ↦ f.hom (x g)
        map_add' := by
          intro x y
          funext g
          exact map_add f.hom (x g) (y g)
        map_smul' := by
          intro r x
          funext g
          exact map_smul f.hom r (x g) }
  comm := by
    intro g
    ext x
    rfl

/-- The cofree `R`-linear `G`-action functor. -/
@[stacks 04JF "cofree algebraic action functor"]
def functor : ModuleCat.{max u v} R ⥤ Action (ModuleCat.{max u v} R) G where
  obj := obj R G
  map := map R G
  map_id := by
    intro M
    ext x
    rfl
  map_comp := by
    intro M N P f g
    ext x
    rfl

/-- The forgetful/cofree Hom equivalence for `R`-linear `G`-actions. -/
@[stacks 04JF "cofree algebraic action Hom equivalence"]
def homEquiv (X : Action (ModuleCat.{max u v} R) G)
    (M : ModuleCat.{max u v} R) :
    ((Action.forget (ModuleCat.{max u v} R) G).obj X ⟶ M) ≃
      (X ⟶ (functor R G).obj M) where
  toFun φ :=
    { hom :=
        ModuleCat.ofHom
          { toFun := fun x g ↦ φ.hom ((X.ρ g).hom x)
            map_add' := by
              intro x y
              funext g
              exact (φ.hom.comp (X.ρ g).hom).map_add x y
            map_smul' := by
              intro r x
              funext g
              exact (φ.hom.comp (X.ρ g).hom).map_smul r x }
      comm := by
        intro g
        ext x
        funext h
        change φ.hom ((X.ρ h).hom ((X.ρ g).hom x)) =
          φ.hom ((X.ρ (h * g)).hom x)
        rw [map_mul]
        rfl }
  invFun ψ :=
    ModuleCat.ofHom
      { toFun := fun x ↦ ψ.hom.hom x 1
        map_add' := by
          intro x y
          exact congrFun (map_add ψ.hom.hom x y) 1
        map_smul' := by
          intro r x
          exact congrFun (map_smul ψ.hom.hom r x) 1 }
  left_inv := by
    intro φ
    ext x
    change φ.hom ((X.ρ 1).hom x) = φ.hom x
    rw [map_one]
    rfl
  right_inv := by
    intro ψ
    ext x
    funext g
    change ψ.hom.hom ((X.ρ g).hom x) 1 = ψ.hom.hom x g
    have h := congrArg (fun f : X.V ⟶ (obj R G M).V ↦ f.hom x 1) (ψ.comm g)
    change ψ.hom.hom ((X.ρ g).hom x) 1 = ψ.hom.hom x (1 * g) at h
    simpa only [one_mul] using h

/-- The cofree action is right adjoint to the forgetful functor. -/
@[stacks 04JF "cofree algebraic action adjunction"]
noncomputable def adjunction :
    Action.forget (ModuleCat.{max u v} R) G ⊣ functor R G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R G
      homEquiv_naturality_left_symm := by
        intro X' X M f g
        ext x
        rfl
      homEquiv_naturality_right := by
        intro X M N f g
        ext x
        rfl }

/-- Evaluation of the action on a cofree object is right translation. -/
@[simp]
theorem rho_apply (M : ModuleCat.{max u v} R) (g h : G) (f : G → M) :
    ((obj R G M).ρ g).hom f h = f (h * g) := rfl

/-- The map of cofree actions is pointwise postcomposition. -/
@[simp]
theorem map_apply {M N : ModuleCat.{max u v} R} (f : M ⟶ N) (x : G → M) (g : G) :
    (map R G f).hom.hom x g = f.hom (x g) := rfl

/-- The forward cofree Hom equivalence evaluates the original map after the action. -/
@[simp]
theorem homEquiv_apply (X : Action (ModuleCat.{max u v} R) G)
    (M : ModuleCat.{max u v} R)
    (φ : (Action.forget (ModuleCat.{max u v} R) G).obj X ⟶ M) (x : X.V) (g : G) :
    ((homEquiv R G X M φ).hom.hom x) g = φ.hom ((X.ρ g).hom x) := rfl

/-- The inverse cofree Hom equivalence is evaluation at the identity of `G`. -/
@[simp]
theorem homEquiv_symm_apply (X : Action (ModuleCat.{max u v} R) G)
    (M : ModuleCat.{max u v} R) (ψ : X ⟶ (functor R G).obj M) (x : X.V) :
    (homEquiv R G X M).symm ψ x = ψ.hom.hom x 1 := rfl

end Cofree

end

end CategoryTheory.Action.ModuleCat
