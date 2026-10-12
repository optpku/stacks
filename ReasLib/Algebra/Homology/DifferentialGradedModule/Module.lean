/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Indexing

/-!
# Right Differential Graded Modules

This leaf owns right modules over a cochain differential graded algebra and
their ordinary category.  Enrichment and shifts live in separate leaves.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- Definition 22.4.1 (1): a right differential graded module over a cochain differential graded
algebra. -/
@[stacks 09JI]
structure DifferentialGradedModule (A : CochainDGAlgebra R) where
  /-- The degree-`n` module. -/
  X : ℤ → ModuleCat.{v} R
  /-- The degree-raising differential. -/
  d (n : ℤ) : X n →ₗ[R] X (n + 1)
  /-- The homogeneous right action. -/
  smul (p i : ℤ) : X p →ₗ[R] A.X i →ₗ[R] X (p + i)
  /-- The differential squares to zero. -/
  d_sq (n : ℤ) (x : X n) : d (n + 1) (d n x) = 0
  /-- The degree-zero unit acts by scalar multiplication. -/
  smul_one (r : R) (p : ℤ) (x : X p) :
    smul p 0 x (r • A.one) = cast (DifferentialGradedModule.zeroActionTarget p) (r • x)
  /-- Multiplication in the algebra acts by successive right actions. -/
  smul_mul (p i j : ℤ) (x : X p) (a : A.X i) (b : A.X j) :
    smul p (i + j) x (A.mul i j a b) =
      cast (DifferentialGradedModule.mulActionTarget p i j) (smul (p + i) j (smul p i x a) b)
  /-- The differential satisfies the graded Leibniz rule for the right action. -/
  comm_d (p i : ℤ) (x : X p) (a : A.X i) :
    d (p + i) (smul p i x a) =
      cast (DifferentialGradedModule.dLeftActionTarget p i) (smul (p + 1) i (d p x) a) +
        (p.negOnePow : R) •
          cast (DifferentialGradedModule.dRightActionTarget p i) (smul p (i + 1) x (A.d i a))

namespace DifferentialGradedModule

variable {A : CochainDGAlgebra R}

/-- Applying a differential twice to a homogeneous element gives zero. -/
theorem d_sq_apply (M : DifferentialGradedModule A) (n : ℤ) (x : M.X n) :
    M.d (n + 1) (M.d n x) = 0 := sorry

/-- Definition 22.4.1 (2): a morphism of right differential graded modules. -/
@[stacks 09JI]
structure Hom (M N : DifferentialGradedModule A) where
  /-- The degree-preserving linear components. -/
  hom (n : ℤ) : M.X n →ₗ[R] N.X n
  /-- Compatibility with the differential. -/
  comm_d (n : ℤ) (x : M.X n) : hom (n + 1) (M.d n x) = N.d n (hom n x)
  /-- Compatibility with the right action. -/
  comm_smul (p i : ℤ) (x : M.X p) (a : A.X i) :
    hom (p + i) (M.smul p i x a) = N.smul p i (hom p x) a

namespace Hom

/-- The identity right-DG-module morphism. -/
def id (M : DifferentialGradedModule A) : Hom M M where
  hom _ := LinearMap.id
  comm_d _ _ := rfl
  comm_smul _ _ _ _ := rfl

/-- Composition of right-DG-module morphisms. -/
def comp {L M N : DifferentialGradedModule A} (g : Hom M N) (f : Hom L M) : Hom L N where
  hom n := (g.hom n).comp (f.hom n)
  comm_d _ _ := sorry
  comm_smul _ _ _ _ := sorry

/-- The degreewise map of the identity morphism. -/
@[simp] theorem id_hom (M : DifferentialGradedModule A) (n : ℤ) :
    (id M).hom n = LinearMap.id := sorry

/-- The identity morphism acts identically on homogeneous elements. -/
@[simp] theorem id_apply (M : DifferentialGradedModule A) (n : ℤ) (x : M.X n) :
    (id M).hom n x = x := sorry

/-- The degreewise map of a composite morphism. -/
@[simp] theorem comp_hom {L M N : DifferentialGradedModule A} (g : Hom M N) (f : Hom L M)
    (n : ℤ) :
    (comp g f).hom n = (g.hom n).comp (f.hom n) := sorry

/-- A composite morphism acts degreewise by function composition. -/
@[simp] theorem comp_apply {L M N : DifferentialGradedModule A} (g : Hom M N) (f : Hom L M)
    (n : ℤ) (x : L.X n) :
    (comp g f).hom n x = g.hom n (f.hom n x) := sorry

end Hom

/-- Right-DG-module morphisms are determined by their homogeneous components. -/
@[ext] theorem hom_ext {M N : DifferentialGradedModule A} {f g : Hom M N}
    (h : ∀ n : ℤ, ∀ x : M.X n, f.hom n x = g.hom n x) : f = g := sorry

/-- A right-DG-module morphism acts degreewise on homogeneous elements. -/
instance {M N : DifferentialGradedModule A} :
    CoeFun (Hom M N) (fun _ ↦ ∀ n : ℤ, M.X n → N.X n) where
  coe f := fun n x ↦ f.hom n x

/-- Coercion to a function is the degreewise linear component. -/
@[simp] theorem coe_apply {M N : DifferentialGradedModule A} (f : Hom M N) (n : ℤ) (x : M.X n) :
    f n x = f.hom n x := sorry

/-- A right-DG-module morphism commutes with the differential. -/
@[simp] theorem map_d_apply {M N : DifferentialGradedModule A} (f : Hom M N) (n : ℤ)
    (x : M.X n) :
    f (n + 1) (M.d n x) = N.d n (f n x) := sorry

/-- A right-DG-module morphism is compatible with the right action. -/
@[simp] theorem map_smul_apply {M N : DifferentialGradedModule A} (f : Hom M N) (p i : ℤ)
    (x : M.X p) (a : A.X i) :
    f (p + i) (M.smul p i x a) = N.smul p i (f p x) a := sorry

/-- Right differential graded modules over `A` form a category. -/
instance instCategory (A : CochainDGAlgebra R) : Category (DifferentialGradedModule A) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp g f
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end DifferentialGradedModule
