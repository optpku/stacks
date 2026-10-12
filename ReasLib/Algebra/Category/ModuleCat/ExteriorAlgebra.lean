/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior algebras in `ModuleCat`

This file bundles the underlying module of the exterior algebra, its degree-one generator, and
its functorial action.  Multiplicative structure remains in the canonical `ExteriorAlgebra` type;
the categorical owner records the module-valued interface used by module presheaves and sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The underlying `R`-module of the exterior algebra of `M`. -/
@[stacks 00DQ "exterior algebra of a bundled module"]
def exteriorAlgebra (M : ModuleCat.{v} R) : ModuleCat.{max u v} R :=
  ModuleCat.of R (ExteriorAlgebra R M)

namespace exteriorAlgebra

/-- The exterior algebra of `M` as a bundled associative `R`-algebra. -/
@[stacks 00DQ "bundled exterior algebra"]
abbrev alg (M : ModuleCat.{v} R) : AlgCat.{max u v} R :=
  AlgCat.of R (ExteriorAlgebra R M)

/-- The canonical degree-one linear map from a module to its exterior algebra. -/
noncomputable def ι (M : ModuleCat.{v} R) : M →ₗ[R] M.exteriorAlgebra :=
  ExteriorAlgebra.ι R

/-- The canonical inclusion as a bundled morphism in a universe containing the scalar ring. -/
noncomputable def ιHom (M : ModuleCat.{max u v} R) : M ⟶ M.exteriorAlgebra :=
  ModuleCat.ofHom (ι M)

/-- The algebra morphism on exterior algebras induced by a module morphism. -/
@[stacks 00DQ "exterior algebra map"]
noncomputable def algMap {M N : ModuleCat.{v} R} (f : M ⟶ N) : alg M ⟶ alg N :=
  AlgCat.ofHom (ExteriorAlgebra.map f.hom)

/-- Exterior-algebra maps preserve identity morphisms. -/
@[simp, stacks 00DQ "identity exterior algebra map"]
theorem algMap_id (M : ModuleCat.{v} R) : algMap (𝟙 M) = 𝟙 (alg M) := by
  ext m
  simp [algMap]

/-- Exterior-algebra maps preserve composition. -/
@[simp, stacks 00DQ "composition of exterior algebra maps"]
theorem algMap_comp {M N P : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ P) :
    algMap (f ≫ g) = algMap f ≫ algMap g := by
  ext m
  simp [algMap]

end exteriorAlgebra

end ModuleCat

namespace AlgCat

/-- The functor sending an `R`-module to its exterior algebra. -/
@[stacks 00DQ "algebra-valued exterior algebra functor"]
noncomputable def exteriorAlgebra (R : Type u) [CommRing R] :
    ModuleCat.{v} R ⥤ AlgCat.{max u v} R where
  obj := ModuleCat.exteriorAlgebra.alg
  map := ModuleCat.exteriorAlgebra.algMap
  map_id := ModuleCat.exteriorAlgebra.algMap_id
  map_comp := ModuleCat.exteriorAlgebra.algMap_comp

end AlgCat

namespace ModuleCat.exteriorAlgebra

variable {R : Type u} [CommRing R]

/-- The underlying module morphism induced by a module morphism. -/
noncomputable def map {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    M.exteriorAlgebra ⟶ N.exteriorAlgebra :=
  ModuleCat.ofHom (algMap f).hom.toLinearMap

/-- The exterior-algebra morphism induced by `f` sends a degree-one generator to the generator
of its image. -/
@[simp]
theorem map_ι {M N : ModuleCat.{v} R} (f : M ⟶ N) (x : M) :
    map f (ι M x) = ι N (f x) := sorry

/-- Exterior algebras carry identity morphisms to identity morphisms. -/
@[simp]
theorem map_id (M : ModuleCat.{v} R) : map (𝟙 M) = 𝟙 M.exteriorAlgebra := sorry

/-- Exterior algebras preserve composition of module morphisms. -/
@[simp]
theorem map_comp {M N P : ModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ P) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- The module-valued exterior-algebra functor, obtained by forgetting the
multiplicative structure of `AlgCat.exteriorAlgebra`. -/
@[stacks 00DQ "module-valued exterior algebra functor"]
noncomputable def functor (R : Type u) [CommRing R] :
    ModuleCat.{v} R ⥤ ModuleCat.{max u v} R :=
  AlgCat.exteriorAlgebra R ⋙
    forget₂ (AlgCat.{max u v} R) (ModuleCat.{max u v} R)

end ModuleCat.exteriorAlgebra
