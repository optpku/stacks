module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products of modules without a same-universe restriction

The monoidal structure on `ModuleCat R` requires the module carrier and the ring to live in the
same universe because its unit is `R`.  The tensor bifunctor itself has no such restriction.  This
file exposes that smaller piece of structure across arbitrary carrier universes; it is the
appropriate owner for constructions, such as total tensor complexes, which never use the
monoidal unit.
-/

@[expose] public section

noncomputable section

universe u v w x y uJ vJ

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat.TensorProduct

variable (R : Type u) [CommRing R]

/-- The tensor product of two `R`-modules in possibly different carrier universes. -/
abbrev obj (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) : ModuleCat.{max v w} R :=
  ModuleCat.of R (_root_.TensorProduct R M N)

/-- The map on tensor products induced by a pair of module morphisms. -/
def map {M M' : ModuleCat.{v} R} {N N' : ModuleCat.{w} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    obj R M N ⟶ obj R M' N' :=
  ModuleCat.ofHom (_root_.TensorProduct.map f.hom g.hom)

/-- Exchange the two middle factors in a fourfold tensor product and insert the Koszul sign
determined by their degrees. -/
def koszulShuffle (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (P : ModuleCat.{x} R) (Q : ModuleCat.{y} R) (degreeN degreeP : ℤ) :
    obj R (obj R M N) (obj R P Q) ⟶ obj R (obj R M P) (obj R N Q) :=
  ModuleCat.ofHom
    ((degreeN * degreeP).negOnePow •
      (_root_.TensorProduct.tensorTensorTensorComm R M N P Q).toLinearMap)

/-- The Koszul shuffle exchanges the middle entries of a pure fourfold tensor. -/
@[simp]
theorem koszulShuffle_tmul (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (P : ModuleCat.{x} R) (Q : ModuleCat.{y} R) (degreeN degreeP : ℤ)
    (m : M) (n : N) (p : P) (q : Q) :
    koszulShuffle R M N P Q degreeN degreeP
        ((m ⊗ₜ[R] n) ⊗ₜ[R] (p ⊗ₜ[R] q)) =
      (degreeN * degreeP).negOnePow • ((m ⊗ₜ[R] p) ⊗ₜ[R] (n ⊗ₜ[R] q)) := sorry

/-- The tensor-product map acts componentwise on pure tensors. -/
@[simp]
theorem map_tmul {M M' : ModuleCat.{v} R} {N N' : ModuleCat.{w} R}
    (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    map R f g (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n := sorry

/-- Tensor product as a bifunctor, without choosing a monoidal unit in `ModuleCat`. -/
@[stacks 09LL "ground tensor bifunctor for modules"]
def functor :
    ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤ ModuleCat.{max v w} R where
  obj M :=
    { obj := obj R M
      map := map R (𝟙 M)
      map_id := sorry
      map_comp := sorry }
  map f :=
    { app := fun N ↦ map R f (𝟙 N)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- The curried tensor-product bifunctor has `obj R M N` as its value at `(M, N)`. -/
@[simp]
theorem functor_obj (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) :
    ((functor.{u, v, w} R).obj M).obj N = obj R M N := sorry

/-- The inner functor acts by the tensor-product map with the identity in the first variable. -/
@[simp]
theorem functor_obj_map (M : ModuleCat.{v} R) {N N' : ModuleCat.{w} R}
    (g : N ⟶ N') :
    ((functor.{u, v, w} R).obj M).map g = map R (𝟙 M) g := sorry

/-- The outer functor acts by the tensor-product map with the identity in the second variable. -/
@[simp]
theorem functor_map {M M' : ModuleCat.{v} R} (f : M ⟶ M')
    (N : ModuleCat.{w} R) :
    ((functor.{u, v, w} R).map f).app N = map R f (𝟙 N) := sorry

/-- Tensoring in the second variable preserves addition of morphisms. -/
instance functorObjAdditive (M : ModuleCat.{v} R) :
    (functor.{u, v, w} R).obj M |>.Additive where
  map_add := sorry

/-- Tensoring in the first variable preserves addition of morphisms. -/
instance functorAdditive : (functor.{u, v, w} R).Additive where
  map_add := sorry

/-- Tensoring a fixed module in the first variable preserves colimits of every size. -/
@[stacks 09LL "module tensor product preserves colimits in the second variable"]
noncomputable instance functorObjPreservesColimits (M : ModuleCat.{v} R) :
    PreservesColimitsOfSize.{uJ, vJ} ((functor.{u, v, w} R).obj M) := sorry

/-- Tensoring a fixed module in the second variable preserves colimits of every size. -/
@[stacks 09LL "module tensor product preserves colimits in the first variable"]
noncomputable instance functorFlipObjPreservesColimits (N : ModuleCat.{w} R) :
    PreservesColimitsOfSize.{uJ, vJ} ((functor.{u, v, w} R).flip.obj N) := sorry

/-- Construct a morphism out of a tensor product from a curried `R`-bilinear map. -/
def lift {M : ModuleCat.{v} R} {N : ModuleCat.{w} R} {P : ModuleCat.{max v w} R}
    (f : M →ₗ[R] N →ₗ[R] P) : obj R M N ⟶ P :=
  ModuleCat.ofHom (_root_.TensorProduct.lift f)

/-- Construct a morphism out of a tensor product from a function and its bilinearity laws. -/
def liftOfBilinear {M : ModuleCat.{v} R} {N : ModuleCat.{w} R}
    {P : ModuleCat.{max v w} R}
    (f : M → N → P)
    (map_add_left : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (map_smul_left : ∀ (r : R) m n, f (r • m) n = r • f m n)
    (map_add_right : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (map_smul_right : ∀ (r : R) m n, f m (r • n) = r • f m n) :
    obj R M N ⟶ P :=
  lift R (LinearMap.mk₂ R f map_add_left map_smul_left map_add_right map_smul_right)

/-- The tensor lift evaluates on a pure tensor by the original bilinear function. -/
@[simp]
theorem lift_tmul {M : ModuleCat.{v} R} {N : ModuleCat.{w} R}
    {P : ModuleCat.{max v w} R}
    (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
    lift R f (m ⊗ₜ[R] n) = f m n := sorry

/-- A lift built from a function and bilinearity laws evaluates as that function on pure
tensors. -/
@[simp]
theorem liftOfBilinear_tmul {M : ModuleCat.{v} R} {N : ModuleCat.{w} R}
    {P : ModuleCat.{max v w} R}
    (f : M → N → P)
    (map_add_left : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
    (map_smul_left : ∀ (r : R) m n, f (r • m) n = r • f m n)
    (map_add_right : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
    (map_smul_right : ∀ (r : R) m n, f m (r • n) = r • f m n)
    (m : M) (n : N) :
    liftOfBilinear R f map_add_left map_smul_left map_add_right map_smul_right
      (m ⊗ₜ[R] n) = f m n := sorry

end ModuleCat.TensorProduct
