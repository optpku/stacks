/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.Left
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The category of left graded modules

Morphisms are `A`-linear maps which preserve every homogeneous piece of the chosen grading.
-/

@[expose] public section

noncomputable section

universe x w v u

open CategoryTheory

namespace GradedModule.Left

variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {κ : Type x} [DecidableEq κ] [AddAction ι κ]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

/-- The additive group structure on a left graded module over a ring. -/
instance instAddCommGroup (M : Left.{x, w, v, u} 𝒜 κ) : AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup A (M := M)

/-- The additive subgroup of `A`-linear maps preserving every homogeneous piece. -/
def homAddSubgroup (M N : Left.{x, w, v, u} 𝒜 κ) : AddSubgroup (M →ₗ[A] N) where
  carrier := {f | ∀ k (x : M), x ∈ M.grading k → f x ∈ N.grading k}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Morphisms of left graded modules are `A`-linear maps preserving the grading. -/
@[stacks 052N "morphisms of left graded modules"]
abbrev Hom (M N : Left.{x, w, v, u} 𝒜 κ) : Type _ := homAddSubgroup M N

namespace Hom

/-- Construct a graded morphism from a grading-preserving `A`-linear map. -/
def ofLinearMap {M N : Left.{x, w, v, u} 𝒜 κ} (f : M →ₗ[A] N)
    (h_map_mem : ∀ k (x : M), x ∈ M.grading k → f x ∈ N.grading k) : Hom M N :=
  ⟨f, h_map_mem⟩

/-- The underlying `A`-linear map of a left graded-module morphism. -/
def toLinearMap {M N : Left.{x, w, v, u} 𝒜 κ} (f : Hom M N) : M →ₗ[A] N :=
  f.1

/-- A left graded-module morphism preserves each homogeneous piece. -/
theorem map_mem {M N : Left.{x, w, v, u} 𝒜 κ} (f : Hom M N)
    {k : κ} {x : M} (hx : x ∈ M.grading k) : toLinearMap f x ∈ N.grading k := sorry

/-- A left graded-module morphism maps each homogeneous piece to the corresponding piece. -/
theorem mapsTo {M N : Left.{x, w, v, u} 𝒜 κ} (f : Hom M N) (k : κ) :
    Set.MapsTo (toLinearMap f) (M.grading k) (N.grading k) := sorry

/-- Left graded-module morphisms are determined by their underlying linear maps. -/
@[ext] theorem ext {M N : Left.{x, w, v, u} 𝒜 κ} {f g : Hom M N}
    (h : ∀ x : M, toLinearMap f x = toLinearMap g x) : f = g := sorry

/-- The identity linear map preserves every homogeneous piece. -/
theorem id_map_mem (M : Left.{x, w, v, u} 𝒜 κ) :
    ∀ k (x : M), x ∈ M.grading k → (LinearMap.id : M →ₗ[A] M) x ∈ M.grading k := sorry

/-- The identity morphism of a left graded module. -/
def id (M : Left.{x, w, v, u} 𝒜 κ) : Hom M M :=
  ofLinearMap LinearMap.id (id_map_mem M)

/-- The composite of two grading-preserving linear maps preserves every homogeneous piece. -/
theorem comp_map_mem {L M N : Left.{x, w, v, u} 𝒜 κ} (g : Hom M N) (f : Hom L M) :
    ∀ k (x : L), x ∈ L.grading k →
      ((toLinearMap g).comp (toLinearMap f)) x ∈ N.grading k := sorry

/-- Composition of left graded-module morphisms. -/
def comp {L M N : Left.{x, w, v, u} 𝒜 κ} (g : Hom M N) (f : Hom L M) : Hom L N :=
  ofLinearMap ((toLinearMap g).comp (toLinearMap f)) (comp_map_mem g f)

end Hom

/-- Left graded modules over a fixed graded algebra form a category. -/
instance instCategory : Category (Left.{x, w, v, u} 𝒜 κ) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

namespace Hom

/-- The underlying linear map of the identity graded-module morphism is `LinearMap.id`. -/
@[simp] theorem toLinearMap_id (M : Left.{x, w, v, u} 𝒜 κ) :
    toLinearMap (𝟙 M) = LinearMap.id := sorry

/-- The underlying linear map of a composite is the composite of underlying linear maps. -/
@[simp] theorem toLinearMap_comp {L M N : Left.{x, w, v, u} 𝒜 κ}
    (f : L ⟶ M) (g : M ⟶ N) :
    toLinearMap (f ≫ g) = (toLinearMap g).comp (toLinearMap f) := sorry

end Hom

/-- The category of left graded modules is preadditive. -/
instance instPreadditive : Preadditive (Left.{x, w, v, u} 𝒜 κ) where
  homGroup M N := inferInstanceAs (AddCommGroup (Hom M N))
  add_comp := sorry
  comp_add := sorry

/-- Forget the grading of a left graded module, retaining its underlying `A`-module. -/
@[stacks 052N "forgetful functor from left graded modules"]
def forget : Left.{x, w, v, u} 𝒜 κ ⥤ ModuleCat A where
  obj M := ModuleCat.of A M
  map f := ModuleCat.ofHom (Hom.toLinearMap f)
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor maps a graded morphism to its underlying linear map. -/
@[simp] theorem forget_map {M N : Left.{x, w, v, u} 𝒜 κ} (f : M ⟶ N) :
    (forget (𝒜 := 𝒜) (κ := κ)).map f = ModuleCat.ofHom (Hom.toLinearMap f) := sorry

/-- Applying the forgetful functor to a morphism acts by its underlying linear map. -/
@[simp] theorem forget_map_apply {M N : Left.{x, w, v, u} 𝒜 κ} (f : M ⟶ N) (m : M) :
    (forget (𝒜 := 𝒜) (κ := κ)).map f m = Hom.toLinearMap f m := sorry

/-- The forgetful functor from left graded modules is faithful. -/
instance forgetFaithful : (forget (𝒜 := 𝒜) (κ := κ)).Faithful where
  map_injective := sorry

/-- The forgetful functor from left graded modules is additive. -/
instance forgetAdditive : (forget (𝒜 := 𝒜) (κ := κ)).Additive where
  map_add := sorry

end GradedModule.Left
