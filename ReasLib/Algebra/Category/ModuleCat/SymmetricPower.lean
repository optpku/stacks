module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import ReasLib.LinearAlgebra.TensorPower.Symmetric.Map
public import ReasLib.LinearAlgebra.TensorPower.Symmetric.UFin

/-!
# Symmetric powers in `ModuleCat`

This file bundles finite symmetric tensor powers as objects and functors in the category of
modules.  The finite index is `SymmetricPower.UFin n`, so its universe follows the coefficient
ring without exposing `ULift` in downstream statements.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u v

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The degree-`n` symmetric tensor power of an object of `ModuleCat R`. -/
@[stacks 01CG "symmetric power of a module"]
def symmetricPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (Sym[R] (SymmetricPower.UFin n) M)

namespace symmetricPower

/-- The universal pure symmetric tensor in the degree-`n` symmetric power of `M`. -/
@[stacks 01CG "pure symmetric tensor"]
noncomputable def mk {M : ModuleCat.{v} R} {n : ℕ} :
    MultilinearMap R (fun _ : SymmetricPower.UFin n ↦ M) (M.symmetricPower n) :=
  SymmetricPower.tprod R

/-- The morphism on degree-`n` symmetric powers induced by a module morphism. -/
@[stacks 01CG "map on symmetric powers"]
noncomputable def map {M N : ModuleCat.{v} R} (f : M ⟶ N) (n : ℕ) :
    M.symmetricPower n ⟶ N.symmetricPower n :=
  ModuleCat.ofHom (SymmetricPower.map (ι := SymmetricPower.UFin n) f.hom)

/-- A symmetric-power morphism acts entrywise on pure symmetric tensors. -/
@[simp, stacks 01CG "symmetric power map on pure tensors"]
theorem map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : ℕ}
    (m : SymmetricPower.UFin n → M) :
    map f n (mk m) = mk (f ∘ m) := sorry

/-- Symmetric powers carry identity morphisms to identity morphisms. -/
@[simp, stacks 01CG "symmetric power map identity"]
theorem map_id (M : ModuleCat.{v} R) (n : ℕ) :
    map (𝟙 M) n = 𝟙 (M.symmetricPower n) := sorry

/-- Symmetric powers preserve composition of module morphisms. -/
@[simp, stacks 01CG "symmetric power map composition"]
theorem map_comp {M N P : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n := sorry

/-- The degree-`n` symmetric-power endofunctor on `ModuleCat R`. -/
@[stacks 01CG "symmetric-power functor on modules"]
noncomputable def functor (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.{v} R ⥤ ModuleCat.{max u v} R where
  obj M := M.symmetricPower n
  map f := map f n
  map_id M := map_id M n
  map_comp f g := map_comp f g n

end symmetricPower

end ModuleCat
