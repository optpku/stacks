/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.NumberTheory.Padics.RingHoms
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

section Cohomology

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- Inverse system of global étale cohomology groups of the stages of a `ℤ_[ℓ]`-sheaf. -/
def cohomologySystem (F : ZEllSheaf X ℓ) (i : ℕ) :
    SequentialInverseSystem AddCommGrpCat.{u} :=
  F.system ⋙ Sheaf.cohomologyAtObjectFunctor X.smallEtaleTopology (globalEtale X) i

/-- Stage `n` of the cohomology inverse system is `H^i(X, F.stage n)`. -/
theorem cohomologySystem_obj (F : ZEllSheaf X ℓ) (i n : ℕ) :
    (F.cohomologySystem i).obj (op n) = (F.stage n).H' i (globalEtale X) := sorry

/-- Transition maps of the cohomology inverse system are `Sheaf.cohomologyMap` of the
stage transitions. -/
theorem cohomologySystem_map (F : ZEllSheaf X ℓ) (i : ℕ) {a b : ℕᵒᵖ} (f : a ⟶ b) :
    (F.cohomologySystem i).map f =
      Sheaf.cohomologyMap (F.system.map f) i (globalEtale X) := sorry

/-- ℓ-adic cohomology `H^i(X, F)` of a `ℤ_[ℓ]`-sheaf, as the inverse limit of the
étale cohomology of its stages. -/
def cohomology (F : ZEllSheaf X ℓ) (i : ℕ) : AddCommGrpCat.{u} :=
  limit (F.cohomologySystem i)

/-- Unfolding of ℓ-adic cohomology as the inverse limit of stagewise étale cohomology. -/
theorem cohomology_eq (F : ZEllSheaf X ℓ) (i : ℕ) :
    F.cohomology i = limit (F.cohomologySystem i) := sorry

/-- Projection from ℓ-adic cohomology onto the étale cohomology of a stage. -/
def cohomology_π (F : ZEllSheaf X ℓ) (i n : ℕ) :
    F.cohomology i ⟶ (F.stage n).H' i (globalEtale X) :=
  limit.π (F.cohomologySystem i) (op n)

/-- The cone projection of ℓ-adic cohomology is the inverse-limit projection of
`cohomologySystem`. -/
theorem cohomology_π_eq (F : ZEllSheaf X ℓ) (i n : ℕ) :
    F.cohomology_π i n = limit.π (F.cohomologySystem i) (op n) := sorry

/-- ℓ-adic cohomology is the inverse limit of `H^i(X, F.stage n)`, equivalently of
the positively indexed stages `H^i(X, F_{n+1})` for `n : ℕ`. -/
theorem cohomology_spec (F : ZEllSheaf X ℓ) (i : ℕ) :
    F.cohomology i = limit (F.cohomologySystem i) ∧
      ∀ n, (F.cohomologySystem i).obj (op n) = (F.stage n).H' i (globalEtale X) := sorry

/-- Scalar-multiplication components by a `ℤ_[ℓ]`-integer on ℓ-adic cohomology. -/
def cohomologySMulπ (F : ZEllSheaf X ℓ) (i : ℕ) (a : ℤ_[ℓ]) :
    (Functor.const ℕᵒᵖ).obj (F.cohomology i) ⟶ F.cohomologySystem i where
  app n := (PadicInt.toZModPow (n.unop + 1) a).val • limit.π (F.cohomologySystem i) n
  naturality := sorry

/-- The cone presenting scalar multiplication by a `ℤ_[ℓ]`-integer on ℓ-adic cohomology. -/
def cohomologySMulCone (F : ZEllSheaf X ℓ) (i : ℕ) (a : ℤ_[ℓ]) :
    Cone (F.cohomologySystem i) where
  pt := F.cohomology i
  π := F.cohomologySMulπ i a

/-- The endomorphism of ℓ-adic cohomology given by scalar multiplication by a
`ℤ_[ℓ]`-integer. -/
def cohomologySMulHom (F : ZEllSheaf X ℓ) (i : ℕ) (a : ℤ_[ℓ]) :
    F.cohomology i ⟶ F.cohomology i :=
  limit.lift (F.cohomologySystem i) (F.cohomologySMulCone i a)

/-- The unit scalar acts as the identity on ℓ-adic cohomology. -/
theorem cohomologySMulHom_one_apply (F : ZEllSheaf X ℓ) (i : ℕ)
    (element : F.cohomology i) :
    F.cohomologySMulHom i 1 element = element := sorry

/-- Multiplication of scalars acts by successive scalar endomorphisms on ℓ-adic cohomology. -/
theorem cohomologySMulHom_mul_apply (F : ZEllSheaf X ℓ) (i : ℕ) (a b : ℤ_[ℓ])
    (element : F.cohomology i) :
    F.cohomologySMulHom i (a * b) element =
      F.cohomologySMulHom i a (F.cohomologySMulHom i b element) := sorry

/-- Addition of scalars acts by pointwise addition on ℓ-adic cohomology. -/
theorem cohomologySMulHom_add_apply (F : ZEllSheaf X ℓ) (i : ℕ) (a b : ℤ_[ℓ])
    (element : F.cohomology i) :
    F.cohomologySMulHom i (a + b) element =
      F.cohomologySMulHom i a element + F.cohomologySMulHom i b element := sorry

/-- The zero scalar acts by zero on ℓ-adic cohomology. -/
theorem cohomologySMulHom_zero_apply (F : ZEllSheaf X ℓ) (i : ℕ)
    (element : F.cohomology i) :
    F.cohomologySMulHom i 0 element = 0 := sorry

/-- The `ℤ_[ℓ]`-module structure on ℓ-adic cohomology, via compatible residue actions. -/
@[implicit_reducible]
def cohomologyModuleStructure (F : ZEllSheaf X ℓ) (i : ℕ) :
    Module ℤ_[ℓ] (F.cohomology i) where
  smul a element := F.cohomologySMulHom i a element
  one_smul := F.cohomologySMulHom_one_apply i
  mul_smul := F.cohomologySMulHom_mul_apply i
  smul_zero a := (F.cohomologySMulHom i a).hom.map_zero
  smul_add a := (F.cohomologySMulHom i a).hom.map_add
  add_smul := F.cohomologySMulHom_add_apply i
  zero_smul := F.cohomologySMulHom_zero_apply i

/-- ℓ-adic cohomology as a `ℤ_[ℓ]`-module. -/
def cohomologyModule (F : ZEllSheaf X ℓ) (i : ℕ) : ModuleCat.{u} ℤ_[ℓ] :=
  @ModuleCat.of ℤ_[ℓ] _ (F.cohomology i) _ (F.cohomologyModuleStructure i)

/-- The underlying additive group of module-valued ℓ-adic cohomology is its inverse limit. -/
theorem cohomologyModule_eq (F : ZEllSheaf X ℓ) (i : ℕ) :
    (forget₂ (ModuleCat.{u} ℤ_[ℓ]) AddCommGrpCat.{u}).obj (F.cohomologyModule i) =
      F.cohomology i := sorry

end Cohomology

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
