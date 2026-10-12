/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Module
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric algebras in `ModuleCat`

This file bundles the symmetric algebra of a module as an object and functor in `ModuleCat`.
The parallel `CommAlgCat` view retains the multiplicative universal-property map, while the
module view is the one used by presheaves and sheaves of modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The symmetric algebra of an object of `ModuleCat R`, regarded as an `R`-module. -/
@[stacks 00DQ "symmetric algebra of a bundled module"]
abbrev symmetricAlgebra (M : ModuleCat.{v} R) : ModuleCat.{max u v} R :=
  ModuleCat.of R (SymmetricAlgebra R M)

namespace symmetricAlgebra

/-- The symmetric algebra of `M` as a bundled commutative `R`-algebra. -/
@[stacks 00DQ "bundled symmetric algebra"]
abbrev alg (M : ModuleCat.{v} R) : CommAlgCat.{max u v} R :=
  CommAlgCat.of R (SymmetricAlgebra R M)

/-- The canonical linear inclusion of a module into its symmetric algebra. -/
noncomputable def ι (M : ModuleCat.{v} R) : M →ₗ[R] M.symmetricAlgebra :=
  SymmetricAlgebra.ι R M

/-- The canonical inclusion as a bundled morphism in a universe containing
the scalar ring. -/
noncomputable def ιHom (M : ModuleCat.{max u v} R) : M ⟶ M.symmetricAlgebra :=
  ModuleCat.ofHom (ι M)

/-- The commutative-algebra morphism on symmetric algebras induced by a module morphism. -/
@[stacks 00DQ "symmetric algebra map"]
noncomputable def algMap {M N : ModuleCat.{v} R} (f : M ⟶ N) : alg M ⟶ alg N :=
  CommAlgCat.ofHom (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f.hom))

/-- Symmetric-algebra maps preserve identity morphisms. -/
@[simp, stacks 00DQ "identity symmetric algebra map"]
theorem algMap_id (M : ModuleCat.{v} R) : algMap (𝟙 M) = 𝟙 (alg M) := by
  ext m
  simp [algMap]

/-- Symmetric-algebra maps preserve composition. -/
@[simp, stacks 00DQ "composition of symmetric algebra maps"]
theorem algMap_comp {M N P : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ P) :
    algMap (f ≫ g) = algMap f ≫ algMap g := by
  ext m
  simp [algMap]

end symmetricAlgebra

end ModuleCat

namespace CommAlgCat

/-- The functor sending an `R`-module to its symmetric algebra. -/
@[stacks 00DQ "commutative-algebra-valued symmetric algebra functor"]
noncomputable def symmetricAlgebra (R : Type u) [CommRing R] :
    ModuleCat.{v} R ⥤ CommAlgCat.{max u v} R where
  obj := ModuleCat.symmetricAlgebra.alg
  map := ModuleCat.symmetricAlgebra.algMap
  map_id := ModuleCat.symmetricAlgebra.algMap_id
  map_comp := ModuleCat.symmetricAlgebra.algMap_comp

end CommAlgCat

namespace ModuleCat.symmetricAlgebra

variable {R : Type u} [CommRing R]

/-- The module morphism on symmetric algebras induced by a module morphism. -/
noncomputable def map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    M.symmetricAlgebra ⟶ N.symmetricAlgebra :=
  ModuleCat.ofHom (algMap f).hom.toLinearMap

/-- A symmetric-algebra morphism agrees with the underlying module morphism on generators. -/
@[simp]
theorem map_ι {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : M) :
    map f (ι M x) = ι N (f x) := sorry

/-- Symmetric algebras carry identity morphisms to identity morphisms. -/
@[simp]
theorem map_id (M : ModuleCat.{v} R) :
    map (𝟙 M) = 𝟙 M.symmetricAlgebra := sorry

/-- Symmetric algebras preserve composition of module morphisms. -/
@[simp]
theorem map_comp {M N P : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- The module-valued symmetric-algebra functor, obtained by forgetting the
multiplicative structure of `CommAlgCat.symmetricAlgebra`. -/
@[stacks 00DQ "module-valued symmetric algebra functor"]
noncomputable def functor (R : Type u) [CommRing R] :
    ModuleCat.{v} R ⥤ ModuleCat.{max u v} R :=
  CommAlgCat.symmetricAlgebra R ⋙
    CommAlgCat.forgetToModule R

end ModuleCat.symmetricAlgebra
