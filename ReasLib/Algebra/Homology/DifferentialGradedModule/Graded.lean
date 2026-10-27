/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Preadditive
public import ReasLib.CategoryTheory.GradedObject.Instances

/-!
# Underlying Graded Modules of Differential Graded Modules

This file owns the external, degree-indexed category of right graded modules over a cochain
differential graded algebra.  Unlike `GradedModule.Right`, this presentation does not first form
the direct sum of the homogeneous pieces.  It is therefore the canonical target for forgetting
the differential of the external presentation `DifferentialGradedModule`.

For admissibility, retaining the graded right action is essential: a splitting in this category
is a graded `A`-module splitting, not merely a degreewise `R`-linear splitting.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- An externally graded right module over `A`, obtained from a differential graded module by
forgetting only its differential. -/
@[stacks 09JT "external graded right modules underlying differential graded modules"]
structure Graded (A : CochainDGAlgebra.{u, v} R) where
  /-- The homogeneous component in degree `n`. -/
  X : ℤ → ModuleCat.{w} R
  /-- The homogeneous right action of `A`. -/
  smul (p i : ℤ) : X p →ₗ[R] A.X i →ₗ[R] X (p + i)
  /-- The degree-zero unit acts by scalar multiplication. -/
  smul_one (r : R) (p : ℤ) (x : X p) :
    smul p 0 x (r • A.one) = cast (DifferentialGradedModule.zeroActionTarget p) (r • x)
  /-- Multiplication in `A` acts by successive right actions. -/
  smul_mul (p i j : ℤ) (x : X p) (a : A.X i) (b : A.X j) :
    smul p (i + j) x (A.mul i j a b) =
      cast (DifferentialGradedModule.mulActionTarget p i j) (smul (p + i) j (smul p i x a) b)

namespace Graded

variable {A : CochainDGAlgebra.{u, v} R}

/-- A morphism of externally graded right `A`-modules is a degree-preserving family of
`R`-linear maps compatible with the homogeneous right action. -/
structure Hom (M N : Graded.{u, v, w} A) where
  /-- The degree-preserving linear components. -/
  hom (n : ℤ) : M.X n →ₗ[R] N.X n
  /-- Compatibility with the homogeneous right action. -/
  comm_smul (p i : ℤ) (x : M.X p) (a : A.X i) :
    hom (p + i) (M.smul p i x a) = N.smul p i (hom p x) a

/-- A morphism of externally graded modules can be applied in every homogeneous degree. -/
instance instCoeFunHom {M N : Graded.{u, v, w} A} :
    CoeFun (Hom M N) (fun _ ↦ ∀ n : ℤ, M.X n → N.X n) where
  coe f n x := f.hom n x

/-- Applying an externally graded map uses its stored homogeneous component. -/
@[simp]
theorem Hom.coe_apply {M N : Graded.{u, v, w} A} (f : Hom M N) (n : ℤ) (x : M.X n) :
    f n x = f.hom n x := rfl

/-- An externally graded map commutes with the homogeneous right action. -/
@[simp]
theorem Hom.map_smul {M N : Graded.{u, v, w} A} (f : Hom M N)
    (p i : ℤ) (x : M.X p) (a : A.X i) :
    f (p + i) (M.smul p i x a) = N.smul p i (f p x) a :=
  f.comm_smul p i x a

/-- The identity morphism of an externally graded right module. -/
def Hom.id (M : Graded.{u, v, w} A) : Hom M M where
  hom _ := LinearMap.id
  comm_smul _ _ _ _ := rfl

/-- Composition of morphisms of externally graded right modules. -/
def Hom.comp {K L M : Graded.{u, v, w} A} (g : Hom L M) (f : Hom K L) : Hom K M where
  hom n := (g.hom n).comp (f.hom n)
  comm_smul p i x a := by
    change g.hom (p + i) (f.hom (p + i) (K.smul p i x a)) =
      M.smul p i (g.hom p (f.hom p x)) a
    rw [f.comm_smul, g.comm_smul]

/-- The degree-`n` component of the identity is the identity linear map. -/
@[simp]
theorem Hom.id_hom (M : Graded.{u, v, w} A) (n : ℤ) :
    (Hom.id M).hom n = LinearMap.id := rfl

/-- Composition is computed by composing the homogeneous components. -/
@[simp]
theorem Hom.comp_hom {K L M : Graded.{u, v, w} A} (g : Hom L M) (f : Hom K L) (n : ℤ) :
    (Hom.comp g f).hom n = (g.hom n).comp (f.hom n) := rfl

/-- Composition acts by ordinary function composition in each degree. -/
@[simp]
theorem Hom.comp_apply {K L M : Graded.{u, v, w} A} (g : Hom L M) (f : Hom K L)
    (n : ℤ) (x : K.X n) :
    Hom.comp g f n x = g n (f n x) := rfl

/-- Morphisms of externally graded modules are determined by their homogeneous components. -/
@[ext]
theorem hom_ext {M N : Graded.{u, v, w} A} {f g : Hom M N}
    (h : ∀ n : ℤ, f.hom n = g.hom n) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      cases hfg
      rfl

/-- Externally graded right modules over `A` form a category. -/
instance instCategory : Category (Graded.{u, v, w} A) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp {_ _} f := by
    apply hom_ext
    intro n
    apply LinearMap.ext
    intro x
    rfl
  comp_id {_ _} f := by
    apply hom_ext
    intro n
    apply LinearMap.ext
    intro x
    rfl
  assoc {_ _ _ _} f g h := by
    apply hom_ext
    intro n
    apply LinearMap.ext
    intro x
    rfl

/-- The zero morphism is zero in every homogeneous degree. -/
instance instZeroHom (M N : Graded.{u, v, w} A) : Zero (Hom M N) where
  zero :=
    { hom := fun _ ↦ 0
      comm_smul p i x a := by
        simp }

/-- Addition of morphisms is computed degreewise. -/
instance instAddHom (M N : Graded.{u, v, w} A) : Add (Hom M N) where
  add f g :=
    { hom := fun n ↦ f.hom n + g.hom n
      comm_smul p i x a := by
        simp [f.comm_smul, g.comm_smul] }

/-- Negation of morphisms is computed degreewise. -/
instance instNegHom (M N : Graded.{u, v, w} A) : Neg (Hom M N) where
  neg f :=
    { hom := fun n ↦ -f.hom n
      comm_smul p i x a := by
        simp [f.comm_smul] }

/-- Subtraction of morphisms is computed degreewise. -/
instance instSubHom (M N : Graded.{u, v, w} A) : Sub (Hom M N) where
  sub f g :=
    { hom := fun n ↦ f.hom n - g.hom n
      comm_smul p i x a := by
        simp [f.comm_smul, g.comm_smul] }

/-- Natural-number scalar multiplication of morphisms is computed degreewise. -/
instance instNatSMulHom (M N : Graded.{u, v, w} A) : SMul ℕ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm_smul p i x a := by
        simp [f.comm_smul] }

/-- Integer scalar multiplication of morphisms is computed degreewise. -/
instance instIntSMulHom (M N : Graded.{u, v, w} A) : SMul ℤ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm_smul p i x a := by
        simp [f.comm_smul] }

/-- The homogeneous component of the zero morphism is zero. -/
@[simp]
theorem zero_hom (M N : Graded.{u, v, w} A) (n : ℤ) :
    (0 : Hom M N).hom n = 0 := rfl

/-- The homogeneous component of a sum is the sum of the components. -/
@[simp]
theorem add_hom {M N : Graded.{u, v, w} A} (f g : Hom M N) (n : ℤ) :
    (f + g).hom n = f.hom n + g.hom n := rfl

/-- The homogeneous component of a negation is the negated component. -/
@[simp]
theorem neg_hom {M N : Graded.{u, v, w} A} (f : Hom M N) (n : ℤ) :
    (-f).hom n = -f.hom n := rfl

/-- Morphisms of externally graded right modules form an additive commutative group. -/
instance instAddCommGroupHom (M N : Graded.{u, v, w} A) : AddCommGroup (Hom M N) :=
  Function.Injective.addCommGroup (fun f : Hom M N ↦ f.hom)
    (fun _ _ h ↦ hom_ext (congrFun h)) rfl
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The category of externally graded right modules is preadditive. -/
instance instPreadditive : Preadditive (Graded.{u, v, w} A) where
  homGroup M N := instAddCommGroupHom M N
  add_comp _ _ _ f g h := by
    apply hom_ext
    intro n
    apply LinearMap.ext
    intro x
    exact (h.hom n).map_add (f.hom n x) (g.hom n x)
  comp_add _ _ _ f g h := by
    apply hom_ext
    intro n
    apply LinearMap.ext
    intro x
    rfl

/-- Evaluation of an externally graded module in degree `n`. -/
def eval (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    Graded.{u, v, w} A ⥤ ModuleCat.{w} R where
  obj M := M.X n
  map f := ModuleCat.ofHom (f.hom n)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Evaluation preserves addition of externally graded module maps. -/
instance eval_additive (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (eval.{u, v, w} A n).Additive where
  map_add {_ _ _ _} := rfl

/-- Forgetting the right action gives the underlying family of homogeneous `R`-modules. -/
def forgetAction (A : CochainDGAlgebra.{u, v} R) :
    Graded.{u, v, w} A ⥤ GradedObject ℤ (ModuleCat.{w} R) where
  obj M n := M.X n
  map f n := ModuleCat.ofHom (f.hom n)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying graded object functor preserves addition. -/
instance forgetAction_additive (A : CochainDGAlgebra.{u, v} R) :
    (forgetAction.{u, v, w} A).Additive where
  map_add {_ _ _ _} := rfl

end Graded

/-- Forgetting the differential of a right differential graded module retains its externally
graded right `A`-module structure. -/
def toGraded {A : CochainDGAlgebra.{u, v} R}
    (M : DifferentialGradedModule.{u, w} A) : Graded.{u, v, w} A where
  X := M.X
  smul := M.smul
  smul_one := M.smul_one
  smul_mul := M.smul_mul

/-- Forgetting the differential of a DG-module morphism retains its degree-preserving
`A`-linear components. -/
def Hom.toGradedMap {A : CochainDGAlgebra.{u, v} R}
    {M N : DifferentialGradedModule.{u, w} A} (f : M ⟶ N) :
    Graded.Hom M.toGraded N.toGraded where
  hom := f.hom
  comm_smul := f.comm_smul

/-- The canonical functor which forgets only the differential of a differential graded module. -/
@[stacks 09JT "forgetful functor to externally graded modules"]
def forgetToGraded (A : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.{u, w} A ⥤ Graded.{u, v, w} A where
  obj := toGraded
  map := Hom.toGradedMap
  map_id _ := by
    apply Graded.hom_ext
    intro n
    rfl
  map_comp _ _ := by
    apply Graded.hom_ext
    intro n
    rfl

/-- Forgetting the differential preserves every homogeneous component of a module. -/
@[simp]
theorem forgetToGraded_obj_X (A : CochainDGAlgebra.{u, v} R)
    (M : DifferentialGradedModule.{u, w} A) (n : ℤ) :
    ((forgetToGraded A).obj M).X n = M.X n := rfl

/-- Forgetting the differential preserves every homogeneous component of a morphism. -/
@[simp]
theorem forgetToGraded_map_hom (A : CochainDGAlgebra.{u, v} R)
    {M N : DifferentialGradedModule.{u, w} A} (f : M ⟶ N) (n : ℤ) :
    ((forgetToGraded A).map f).hom n = f.hom n := rfl

/-- The functor forgetting the differential is faithful. -/
instance forgetToGraded_faithful (A : CochainDGAlgebra.{u, v} R) :
    Functor.Faithful (forgetToGraded.{u, v, w} A) where
  map_injective {_ _} f g h := by
    cases f with
    | mk f fd fa =>
      cases g with
      | mk g gd ga =>
        have hfg : f = g := congrArg Graded.Hom.hom h
        cases hfg
        rfl

/-- The functor forgetting the differential preserves addition. -/
instance forgetToGraded_additive (A : CochainDGAlgebra.{u, v} R) :
    (forgetToGraded.{u, v, w} A).Additive where
  map_add {_ _ _ _} := by
    apply Graded.hom_ext
    intro n
    rfl

end DifferentialGradedModule
