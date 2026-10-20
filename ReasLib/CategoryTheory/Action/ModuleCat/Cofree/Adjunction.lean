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
            map_add' := sorry
            map_smul' := sorry }
      map_one' := sorry
      map_mul' := sorry }

/-- A module morphism acts on cofree actions by postcomposition. -/
def map {M N : ModuleCat.{max u v} R} (f : M ⟶ N) : obj R G M ⟶ obj R G N where
  hom :=
    ModuleCat.ofHom
      { toFun := fun x g ↦ f.hom (x g)
        map_add' := sorry
        map_smul' := sorry }
  comm := sorry

/-- The cofree `R`-linear `G`-action functor. -/
@[stacks 04JF "cofree algebraic action functor"]
def functor : ModuleCat.{max u v} R ⥤ Action (ModuleCat.{max u v} R) G where
  obj := obj R G
  map := map R G
  map_id := sorry
  map_comp := sorry

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
            map_add' := sorry
            map_smul' := sorry }
      comm := sorry }
  invFun ψ :=
    ModuleCat.ofHom
      { toFun := fun x ↦ ψ.hom.hom x 1
        map_add' := sorry
        map_smul' := sorry }
  left_inv := sorry
  right_inv := sorry

/-- The cofree action is right adjoint to the forgetful functor. -/
@[stacks 04JF "cofree algebraic action adjunction"]
noncomputable def adjunction :
    Action.forget (ModuleCat.{max u v} R) G ⊣ functor R G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R G
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Evaluation of the action on a cofree object is right translation. -/
@[simp]
theorem rho_apply (M : ModuleCat.{max u v} R) (g h : G) (f : G → M) :
    ((obj R G M).ρ g).hom f h = f (h * g) := sorry

/-- The map of cofree actions is pointwise postcomposition. -/
@[simp]
theorem map_apply {M N : ModuleCat.{max u v} R} (f : M ⟶ N) (x : G → M) (g : G) :
    (map R G f).hom.hom x g = f.hom (x g) := sorry

/-- The forward cofree Hom equivalence evaluates the original map after the action. -/
@[simp]
theorem homEquiv_apply (X : Action (ModuleCat.{max u v} R) G)
    (M : ModuleCat.{max u v} R)
    (φ : (Action.forget (ModuleCat.{max u v} R) G).obj X ⟶ M) (x : X.V) (g : G) :
    ((homEquiv R G X M φ).hom.hom x) g = φ.hom ((X.ρ g).hom x) := sorry

/-- The inverse cofree Hom equivalence is evaluation at the identity of `G`. -/
@[simp]
theorem homEquiv_symm_apply (X : Action (ModuleCat.{max u v} R) G)
    (M : ModuleCat.{max u v} R) (ψ : X ⟶ (functor R G).obj M) (x : X.V) :
    (homEquiv R G X M).symm ψ x = ψ.hom.hom x 1 := sorry

end Cofree

end

end CategoryTheory.Action.ModuleCat
