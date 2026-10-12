/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.AlgCat.TensorAlgebra

/-!
# Tensor algebras in `ModuleCat`

This file obtains the tensor algebra and its functorial action from `AlgCat.tensorAlgebra`, then
forgets only the multiplicative structure needed neither by module presheaves nor module sheaves.
Thus the universal property remains owned by Mathlib, while this file supplies the missing
module-valued interface.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The tensor algebra of an object of `ModuleCat R`, regarded as an `R`-module. -/
abbrev tensorAlgebra (M : ModuleCat.{v} R) : ModuleCat.{max u v} R :=
  (forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R)).obj
    ((AlgCat.tensorAlgebra R).obj M)

namespace tensorAlgebra

/-- The tensor algebra of `M` as the canonical bundled associative `R`-algebra. -/
abbrev alg (M : ModuleCat.{v} R) : AlgCat.{max u v} R :=
  (AlgCat.tensorAlgebra R).obj M

/-- The canonical linear inclusion of a module into its tensor algebra. -/
def ι (M : ModuleCat.{v} R) : M →ₗ[R] M.tensorAlgebra :=
  TensorAlgebra.ι R

/-- The canonical inclusion as a bundled morphism when the ring and module share a universe. -/
def ιHom (M : ModuleCat.{u} R) : M ⟶ M.tensorAlgebra :=
  (AlgCat.tensorAlgebraAdj R).unit.app M

/-- The bundled canonical inclusion acts as the usual tensor-algebra linear inclusion. -/
@[simp]
theorem ιHom_apply (M : ModuleCat.{u} R) (m : M) : ιHom M m = ι M m := sorry

/-- The canonical algebra morphism on tensor algebras induced by a module morphism. -/
def algMap {M N : ModuleCat.{v} R} (f : M ⟶ N) : alg M ⟶ alg N :=
  (AlgCat.tensorAlgebra R).map f

/-- The module morphism on tensor algebras induced by a module morphism. -/
def map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    M.tensorAlgebra ⟶ N.tensorAlgebra :=
  (forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R)).map (algMap f)

/-- The induced tensor-algebra map sends a degree-one generator to the image generator. -/
@[simp]
theorem map_ι {M N : ModuleCat.{v} R} (f : M ⟶ N) (m : M) :
    map f (ι M m) = ι N (f m) := sorry

/-- Tensor algebras carry identity module morphisms to identity morphisms. -/
@[simp]
theorem map_id (M : ModuleCat.{v} R) : map (𝟙 M) = 𝟙 M.tensorAlgebra := sorry

/-- Tensor algebras preserve composition of module morphisms. -/
@[simp]
theorem map_comp {M N P : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- The module-valued tensor-algebra functor, obtained from Mathlib's algebra-valued functor. -/
def functor (R : Type u) [CommRing R] :
    ModuleCat.{v} R ⥤ ModuleCat.{max u v} R :=
  AlgCat.tensorAlgebra R ⋙
    forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R)

end tensorAlgebra

end ModuleCat
