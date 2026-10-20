module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of sheaves of modules

This leaf packages site cohomology of sheaves of modules through the underlying additive sheaf,
and the resulting sequential inverse systems of cohomology groups.
-/

@[expose] public section

open Opposite

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/-- The degree-`p` site cohomology functor on sheaves of `A`-modules, computed after forgetting
to additive sheaves. -/
abbrev siteModuleCohomologyFunctor (p : ℕ) :
    Sheaf J (ModuleCat A) ⥤ AddCommGrpCat.{max u v w} :=
  sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat) ⋙ Sheaf.functorH J p

/-- The sequential inverse system obtained by applying degree-`p` module-sheaf cohomology at
every stage. -/
abbrev siteModuleCohomologyTower
    (ℱ : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p : ℕ) :
    SequentialInverseSystem AddCommGrpCat.{max u v w} :=
  ℱ ⋙ siteModuleCohomologyFunctor p

/-- Evaluating a module-sheaf cohomology tower is the same as applying cohomology to the
corresponding stage of the inverse system. -/
@[simp]
theorem siteModuleCohomologyTower_obj
    (ℱ : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p : ℕ) (n : ℕᵒᵖ) :
    (siteModuleCohomologyTower ℱ p).obj n =
      (siteModuleCohomologyFunctor p).obj (ℱ.obj n) := sorry

/-- The transition map in a module-sheaf cohomology tower is cohomology applied to the original
transition map. -/
@[simp]
theorem siteModuleCohomologyTower_map
    (ℱ : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p : ℕ)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    (siteModuleCohomologyTower ℱ p).map f =
      (siteModuleCohomologyFunctor p).map (ℱ.map f) := sorry

/-! ## The canonical module-valued cohomology functor -/

/-- Scalar multiplication on a sheaf of `A`-modules as a canonical endomorphism. -/
abbrev moduleSheafScalarEndomorphism
    (a : A) (ℱ : Sheaf J (ModuleCat A)) : ℱ ⟶ ℱ :=
  a • 𝟙 ℱ

/-- Morphisms of sheaves of `A`-modules commute with scalar endomorphisms. -/
theorem moduleSheafScalarEndomorphism_naturality
    (a : A) {ℱ 𝒢 : Sheaf J (ModuleCat A)} (φ : ℱ ⟶ 𝒢) :
    moduleSheafScalarEndomorphism a ℱ ≫ φ =
      φ ≫ moduleSheafScalarEndomorphism a 𝒢 := sorry

/-- The action of `A` on site cohomology induced by scalar endomorphisms of a module sheaf. -/
abbrev siteModuleCohomologySMul
    (p : ℕ) (ℱ : Sheaf J (ModuleCat A)) (a : A) :
    ((siteModuleCohomologyFunctor p).obj ℱ) →
      ((siteModuleCohomologyFunctor p).obj ℱ) :=
  ((siteModuleCohomologyFunctor p).map
    (moduleSheafScalarEndomorphism a ℱ)).hom

/-- Forgetting module sheaves to additive sheaves is additive after sheaf composition. -/
instance sheafCompose_moduleToAdd_additive :
    (sheafCompose J (forget₂ (ModuleCat A) AddCommGrpCat)).Additive := sorry

/-- The additive site-cohomology functor preserves addition of morphisms. -/
instance siteModuleCohomologyFunctor_additive (p : ℕ) :
    (siteModuleCohomologyFunctor (J := J) (A := A) p).Additive := sorry

/-- Site cohomology has the scalar action induced by scalar endomorphisms of module sheaves. -/
instance siteModuleCohomologySMul_inst
    (p : ℕ) (ℱ : Sheaf J (ModuleCat A)) :
    SMul A ((siteModuleCohomologyFunctor p).obj ℱ) where
  smul := siteModuleCohomologySMul p ℱ

/-- Scalar multiplication distributes over addition on module-sheaf cohomology. -/
theorem siteModuleCohomology_smul_add
    (p : ℕ) (ℱ : Sheaf J (ModuleCat A)) (a : A)
    (x y : (siteModuleCohomologyFunctor p).obj ℱ) :
    a • (x + y) = a • x + a • y := sorry

/-- Addition of scalars distributes over module-sheaf cohomology. -/
theorem siteModuleCohomology_add_smul
    (p : ℕ) (ℱ : Sheaf J (ModuleCat A)) (a b : A)
    (x : (siteModuleCohomologyFunctor p).obj ℱ) :
    (a + b) • x = a • x + b • x := sorry

/-- Multiplication of scalars is compatible with their action on module-sheaf cohomology. -/
theorem siteModuleCohomology_mul_smul
    (p : ℕ) (ℱ : Sheaf J (ModuleCat A)) (a b : A)
    (x : (siteModuleCohomologyFunctor p).obj ℱ) :
    (a * b) • x = a • b • x := sorry

/-- The unit scalar acts trivially on module-sheaf cohomology. -/
theorem siteModuleCohomology_one_smul
    (p : ℕ) (ℱ : Sheaf J (ModuleCat A))
    (x : (siteModuleCohomologyFunctor p).obj ℱ) :
    (1 : A) • x = x := sorry

/-- Site cohomology of a sheaf of `A`-modules has its canonical `A`-module structure. -/
@[stacks 0GYM "module structure on cohomology of module sheaves"]
instance siteModuleCohomologyModule
    (p : ℕ) (ℱ : Sheaf J (ModuleCat A)) :
    Module A ((siteModuleCohomologyFunctor p).obj ℱ) :=
  Module.ofMinimalAxioms
    (siteModuleCohomology_smul_add p ℱ)
    (siteModuleCohomology_add_smul p ℱ)
    (siteModuleCohomology_mul_smul p ℱ)
    (siteModuleCohomology_one_smul p ℱ)

/-- A cohomology map induced by a morphism of module sheaves respects scalar multiplication. -/
theorem siteModuleCohomologyMap_smul
    (p : ℕ) {ℱ 𝒢 : Sheaf J (ModuleCat A)} (φ : ℱ ⟶ 𝒢)
    (a : A) (x : (siteModuleCohomologyFunctor p).obj ℱ) :
    ((siteModuleCohomologyFunctor p).map φ).hom (a • x) =
      a • ((siteModuleCohomologyFunctor p).map φ).hom x := sorry

/-- The map on site cohomology induced by a morphism of module sheaves, as an `A`-linear map. -/
abbrev siteModuleCohomologyMapLinear
    (p : ℕ) {ℱ 𝒢 : Sheaf J (ModuleCat A)} (φ : ℱ ⟶ 𝒢) :
    ((siteModuleCohomologyFunctor p).obj ℱ) →ₗ[A]
      ((siteModuleCohomologyFunctor p).obj 𝒢) where
  toFun := ((siteModuleCohomologyFunctor p).map φ).hom
  map_add' := ((siteModuleCohomologyFunctor p).map φ).hom.map_add
  map_smul' := siteModuleCohomologyMap_smul p φ

/-- The linear cohomology map agrees pointwise with the underlying additive cohomology map. -/
@[simp]
theorem siteModuleCohomologyMapLinear_apply
    (p : ℕ) {ℱ 𝒢 : Sheaf J (ModuleCat A)} (φ : ℱ ⟶ 𝒢)
    (x : (siteModuleCohomologyFunctor p).obj ℱ) :
    siteModuleCohomologyMapLinear p φ x =
      ((siteModuleCohomologyFunctor p).map φ).hom x := sorry

/-- The linear cohomology map of an identity morphism is the identity. -/
theorem siteModuleCohomologyMapLinear_id
    (p : ℕ) (ℱ : Sheaf J (ModuleCat A)) :
    siteModuleCohomologyMapLinear p (𝟙 ℱ) = LinearMap.id := sorry

/-- Linear cohomology maps preserve composition. -/
theorem siteModuleCohomologyMapLinear_comp
    (p : ℕ) {ℱ 𝒢 ℋ : Sheaf J (ModuleCat A)}
    (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ ℋ) :
    siteModuleCohomologyMapLinear p (φ ≫ ψ) =
      (siteModuleCohomologyMapLinear p ψ).comp
        (siteModuleCohomologyMapLinear p φ) := sorry

/-- The identity law for the module-valued site-cohomology functor. -/
theorem siteModuleCohomologyModuleMap_id
    (p : ℕ) (ℱ : Sheaf J (ModuleCat A)) :
    ModuleCat.ofHom (siteModuleCohomologyMapLinear p (𝟙 ℱ)) =
      𝟙 (ModuleCat.of A ((siteModuleCohomologyFunctor p).obj ℱ)) := sorry

/-- The composition law for the module-valued site-cohomology functor. -/
theorem siteModuleCohomologyModuleMap_comp
    (p : ℕ) {ℱ 𝒢 ℋ : Sheaf J (ModuleCat A)}
    (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ ℋ) :
    ModuleCat.ofHom (siteModuleCohomologyMapLinear p (φ ≫ ψ)) =
      ModuleCat.ofHom (siteModuleCohomologyMapLinear p φ) ≫
        ModuleCat.ofHom (siteModuleCohomologyMapLinear p ψ) := sorry

/-- Site cohomology of sheaves of `A`-modules as a functor valued in `ModuleCat A`. -/
@[stacks 0GYM "module-valued cohomology functor"]
noncomputable def siteModuleCohomologyModuleFunctor (p : ℕ) :
    Sheaf J (ModuleCat A) ⥤ ModuleCat A where
  obj ℱ := ModuleCat.of A ((siteModuleCohomologyFunctor p).obj ℱ)
  map φ := ModuleCat.ofHom (siteModuleCohomologyMapLinear p φ)
  map_id := siteModuleCohomologyModuleMap_id p
  map_comp := siteModuleCohomologyModuleMap_comp p

/-- The module-valued cohomology functor has the expected underlying map on elements. -/
@[simp]
theorem siteModuleCohomologyModuleFunctor_map_apply
    (p : ℕ) {ℱ 𝒢 : Sheaf J (ModuleCat A)} (φ : ℱ ⟶ 𝒢)
    (x : (siteModuleCohomologyFunctor p).obj ℱ) :
    ((siteModuleCohomologyModuleFunctor p).map φ).hom x =
      ((siteModuleCohomologyFunctor p).map φ).hom x := sorry

/-- The sequential module-valued cohomology system of a module-sheaf inverse system. -/
@[stacks 0GYM "module-valued cohomology inverse system"]
abbrev siteModuleCohomologyModuleTower
    (ℱ : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p : ℕ) :
    SequentialInverseSystem (ModuleCat A) :=
  ℱ ⋙ siteModuleCohomologyModuleFunctor p

/-- A transition in the module-valued cohomology system as a linear map. -/
abbrev siteModuleCohomologyTransitionMapLinear
    (ℱ : SequentialInverseSystem (Sheaf J (ModuleCat A)))
    (p : ℕ) {i j : ℕ} (hij : i ≤ j) :
    ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op j))) →ₗ[A]
      ((siteModuleCohomologyFunctor p).obj (ℱ.obj (op i))) :=
  siteModuleCohomologyMapLinear p (ℱ.transitionMap hij)

/-- Module-valued and additive cohomology transition maps agree pointwise. -/
@[simp]
theorem siteModuleCohomologyModuleTower_transitionMap_apply
    (ℱ : SequentialInverseSystem (Sheaf J (ModuleCat A)))
    (p : ℕ) {i j : ℕ} (hij : i ≤ j)
    (x : (siteModuleCohomologyFunctor p).obj (ℱ.obj (op j))) :
    ((siteModuleCohomologyModuleTower ℱ p).transitionMap hij).hom x =
      ((siteModuleCohomologyTower ℱ p).transitionMap hij).hom x := sorry

namespace SiteModuleCohomology

/-- The exact degree-`q` cohomology group of the `n`-th member of a family of module sheaves. -/
@[stacks 0GYM "graded ideal-power cohomology piece"]
abbrev piece
    (K : ℕ → Sheaf J (ModuleCat A)) (q n : ℕ) : Type (max u v w) :=
  ((siteModuleCohomologyModuleFunctor q).obj (K n) : Type (max u v w))

/-- The direct sum of exact degree-`q` cohomology groups of a family of module sheaves. -/
@[stacks 0GYM "graded direct sum of ideal-power cohomology"]
abbrev directSum
    (K : ℕ → Sheaf J (ModuleCat A)) (q : ℕ) : Type (max u v w) :=
  DirectSum ℕ (piece K q)

/-- The degree-`n` homogeneous subgroup in the direct sum of exact degree-`q` cohomology. -/
@[stacks 0GYM "grading on ideal-power cohomology"]
abbrev grade
    (K : ℕ → Sheaf J (ModuleCat A)) (q n : ℕ) :
    AddSubgroup (directSum K q) :=
  AddMonoidHom.range (DirectSum.of (piece K q) n)

end SiteModuleCohomology



end CategoryTheory
