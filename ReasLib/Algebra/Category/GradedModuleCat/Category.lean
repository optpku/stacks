module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.Algebra.Group.Action.NatInt

@[expose] public section

open CategoryTheory

universe u

/-- Integer-graded modules over a nonnegatively graded commutative ring, with their specified
internal gradings and homogeneous scalar actions. -/
def GradedModuleCat {A : Type u} [CommRing A]
    (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] : Type (u + 1) :=
  Σ M : ModuleCat.{u} A,
    {ℳ : ℤ → Submodule ℤ M // DirectSum.IsInternal ℳ ∧ SetLike.GradedSMul 𝒜 ℳ}

namespace GradedModuleCat

variable {A : Type u} [CommRing A]
variable {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]

/-- The underlying module of a graded module. -/
abbrev module (M : GradedModuleCat 𝒜) : ModuleCat.{u} A := M.1

/-- The specified homogeneous pieces of a graded module. -/
abbrev grading (M : GradedModuleCat 𝒜) : ℤ → Submodule ℤ M.module := M.2.1

/-- Construct a graded module from a module and a specified compatible internal grading. -/
def of (M : ModuleCat.{u} A) (ℳ : ℤ → Submodule ℤ M)
    (h_internal : DirectSum.IsInternal ℳ) (h_smul : SetLike.GradedSMul 𝒜 ℳ) :
    GradedModuleCat 𝒜 :=
  ⟨M, ℳ, h_internal, h_smul⟩

/-- The scalar action of a graded module sends homogeneous elements to the summed degree. -/
instance gradedSMul (M : GradedModuleCat 𝒜) : SetLike.GradedSMul 𝒜 M.grading :=
  M.2.2.2

/-- Graded morphisms are linear maps preserving every homogeneous piece. -/
def Hom (M N : GradedModuleCat 𝒜) : Type u :=
  {f : M.module →ₗ[A] N.module //
    ∀ degree (element : M.module), element ∈ M.grading degree → f element ∈ N.grading degree}

namespace Hom

/-- Bundle a grading-preserving linear map as a graded morphism. -/
def ofLinearMap {M N : GradedModuleCat 𝒜} (f : M.module →ₗ[A] N.module)
    (h_degree : ∀ degree (element : M.module),
      element ∈ M.grading degree → f element ∈ N.grading degree) : Hom M N :=
  ⟨f, h_degree⟩

/-- The underlying linear map of a graded morphism. -/
def toLinearMap {M N : GradedModuleCat 𝒜} (f : Hom M N) : M.module →ₗ[A] N.module :=
  f.1

/-- The identity graded morphism is the identity linear map. -/
def id (M : GradedModuleCat 𝒜) : Hom M M :=
  ofLinearMap LinearMap.id (fun _ _ h_mem ↦ h_mem)

/-- Composition of graded morphisms is composition of their underlying linear maps. -/
def comp {M N P : GradedModuleCat 𝒜} (f : Hom M N) (g : Hom N P) : Hom M P :=
  ofLinearMap (g.toLinearMap.comp f.toLinearMap)
    (fun degree element h_mem ↦ g.2 degree (f.1 element) (f.2 degree element h_mem))

/-- Composing the identity with a graded morphism leaves it unchanged. -/
theorem id_comp {M N : GradedModuleCat 𝒜} (f : Hom M N) : comp (id M) f = f := sorry

/-- Composing a graded morphism with the identity leaves it unchanged. -/
theorem comp_id {M N : GradedModuleCat 𝒜} (f : Hom M N) : comp f (id N) = f := sorry

/-- Composition of graded morphisms is associative. -/
theorem assoc {M N P Q : GradedModuleCat 𝒜}
    (f : Hom M N) (g : Hom N P) (h : Hom P Q) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- Graded modules form a category with grading-preserving linear maps. -/
instance category : Category.{u} (GradedModuleCat 𝒜) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Forgetting the grading sends the graded identity to the module identity. -/
theorem forget_map_id (M : GradedModuleCat 𝒜) :
    ModuleCat.ofHom (Hom.toLinearMap (𝟙 M)) = 𝟙 M.module := sorry

/-- Forgetting the grading preserves composition. -/
theorem forget_map_comp {M N P : GradedModuleCat 𝒜} (f : M ⟶ N) (g : N ⟶ P) :
    ModuleCat.ofHom (Hom.toLinearMap (f ≫ g)) =
      ModuleCat.ofHom (Hom.toLinearMap f) ≫ ModuleCat.ofHom (Hom.toLinearMap g) := sorry

/-- The forgetful functor sends a graded module to its underlying module. -/
def forget : GradedModuleCat 𝒜 ⥤ ModuleCat.{u} A where
  obj := module
  map f := ModuleCat.ofHom (Hom.toLinearMap f)
  map_id := forget_map_id
  map_comp := forget_map_comp

/-- The full subcategory of graded modules whose underlying modules are finite. -/
abbrev FG (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] :=
  ObjectProperty.FullSubcategory (C := GradedModuleCat 𝒜)
    (fun M ↦ Module.Finite A M.module)

end GradedModuleCat
