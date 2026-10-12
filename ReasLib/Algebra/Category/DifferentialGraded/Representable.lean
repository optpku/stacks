/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Closed
public import ReasLib.Algebra.Category.DifferentialGraded.Endomorphism
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Module

/-!
# Representable Modules in a Differential Graded Category

For a fixed object `x`, homogeneous precomposition makes `Hom(x, y)` a right module over the
endomorphism DGA of `x`.  Closed degree-zero postcomposition packages these modules into the
representable functor on the closed category.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v} [D : DifferentialGradedCategory.{u, v, w} R C]

open scoped DifferentialGradedCategory

/-- The value of the right endomorphism action on a homogeneous morphism. -/
def representableActionValue (x y : C) (p q : ℤ)
    (f : homComponent x y p) (a : homComponent x x q) : homComponent x y (p + q) :=
  @castHom ℤ (fun n : ℤ ↦ x ⟶[n] y) (q + p) (p + q)
    (Int.add_comm q p) (D.comp f a)

/-- Homogeneous precomposition as the bilinear right action of `endomorphismDGA x` on
`Hom(x, y)`. -/
def representableAction (x y : C) (p q : ℤ) :
    homComponent x y p →ₗ[R] homComponent x x q →ₗ[R] homComponent x y (p + q) where
  toFun := fun f ↦
    { toFun := representableActionValue x y p q f
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- The representable right differential graded module `Hom(x, y)` over `endomorphismDGA x`. -/
@[stacks 09LE]
def representableModule (x y : C) : DifferentialGradedModule (endomorphismDGA x) where
  X := homComponent x y
  d := homDifferential x y
  smul := representableAction x y
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The degree-`n` component of the representable module is the homogeneous hom module. -/
@[simp] theorem representableModule_X (x y : C) (n : ℤ) :
    (representableModule x y).X n = homComponent x y n := sorry

/-- The differential of the representable module is the differential on homogeneous morphisms.
-/
@[simp] theorem representableModule_d (x y : C) (n : ℤ) :
    (representableModule x y).d n = homDifferential x y n := sorry

/-- The right action on the representable module is homogeneous precomposition. -/
@[simp] theorem representableModule_smul (x y : C) (p q : ℤ)
    (f : homComponent x y p) (a : homComponent x x q) :
    (representableModule x y).smul p q f a = representableActionValue x y p q f a := sorry

/-- The value of homogeneous postcomposition by a closed degree-zero morphism. -/
def representablePostcompValue {x y z : C} (f : CompHom y z) (n : ℤ)
    (g : homComponent x y n) : homComponent x z n :=
  @castHom ℤ (fun k : ℤ ↦ x ⟶[k] z) (n + 0) n
    (Int.add_zero n) (D.comp f.val g)

/-- Postcomposition by a closed degree-zero morphism as a homogeneous linear map. -/
def representablePostcomp {x y z : C} (f : CompHom y z) (n : ℤ) :
    homComponent x y n →ₗ[R] homComponent x z n where
  toFun := representablePostcompValue f n
  map_add' := sorry
  map_smul' := sorry

/-- Postcomposition is a morphism of representable right differential graded modules. -/
def representableMap (x : C) {y z : C} (f : CompHom y z) :
    representableModule x y ⟶ representableModule x z where
  hom := representablePostcomp f
  comm_d := sorry
  comm_smul := sorry

/-- The degree-`n` component of a representable map is homogeneous postcomposition. -/
@[simp] theorem representableMap_hom (x : C) {y z : C} (f : CompHom y z) (n : ℤ) :
    (representableMap x f).hom n = representablePostcomp f n := sorry

/-- Evaluating a representable map is homogeneous postcomposition. -/
@[simp] theorem representableMap_apply (x : C) {y z : C} (f : CompHom y z)
    (n : ℤ) (g : homComponent x y n) :
    (representableMap x f).hom n g = representablePostcompValue f n g := sorry

/-- The representable map of an identity is the identity module morphism. -/
@[simp] theorem representableMap_id (x y : C) :
    representableMap x (CompHom.id y) = 𝟙 (representableModule x y) := sorry

/-- Representable maps preserve composition. -/
@[simp] theorem representableMap_comp (x : C) {y z t : C}
    (f : CompHom y z) (g : CompHom z t) :
    representableMap x (CompHom.comp f g) = representableMap x f ≫ representableMap x g := sorry

/-- The right-module-valued representable functor based at `x`. -/
@[stacks 09LE]
def representableFunctor (x : C) :
    Comp R C ⥤ DifferentialGradedModule (endomorphismDGA x) where
  obj y := representableModule x y
  map f := representableMap x f
  map_id y := representableMap_id x y
  map_comp f g := representableMap_comp x f g

/-- The representable functor sends `y` to `Hom(x, y)`. -/
@[simp] theorem representableFunctor_obj (x : C) (y : Comp R C) :
    (representableFunctor x).obj y = representableModule x y := sorry

/-- The representable functor sends a closed map to homogeneous postcomposition. -/
@[simp] theorem representableFunctor_map (x : C) {y z : Comp R C} (f : y ⟶ z) :
    (representableFunctor x).map f = representableMap x f := sorry

end DifferentialGradedCategory
