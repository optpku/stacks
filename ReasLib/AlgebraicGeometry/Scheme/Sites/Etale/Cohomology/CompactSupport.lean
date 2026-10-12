/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Adic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

section CompactSupport

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {X : SchemeOverField k} [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})]

/-- Extension by zero of a stage of a `ℤ_[ℓ]`-sheaf along the interior of a
compactification. -/
def extensionByZeroStage (F : ZEllSheaf X.left ℓ) (n : ℕ) :
    Sheaf P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u} :=
  (etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u}).obj (F.stage n)

/-- Unfolding of extension by zero of a stage. -/
theorem extensionByZeroStage_eq (F : ZEllSheaf X.left ℓ) (n : ℕ) :
    extensionByZeroStage P F n =
      (etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u}).obj
        (F.stage n) := sorry

/-- Compactly supported étale cohomology of a stage, as cohomology of its
extension by zero on a compactification. -/
def stageCohomologyCompactSupport (F : ZEllSheaf X.left ℓ) (n i : ℕ) :
    AddCommGrpCat.{u} :=
  (extensionByZeroStage P F n).H' i (globalEtale P.obj.right.left)

/-- Unfolding of stagewise compactly supported cohomology. -/
theorem stageCohomologyCompactSupport_eq (F : ZEllSheaf X.left ℓ) (n i : ℕ) :
    stageCohomologyCompactSupport P F n i =
      (extensionByZeroStage P F n).H' i (globalEtale P.obj.right.left) := sorry

/-- Inverse system of compactly supported étale cohomology groups of the stages of a
`ℤ_[ℓ]`-sheaf. -/
def cohomologyCompactSupportSystem (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    SequentialInverseSystem AddCommGrpCat.{u} :=
  F.system ⋙ etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u} ⋙
    Sheaf.cohomologyAtObjectFunctor P.obj.right.left.smallEtaleTopology
      (globalEtale P.obj.right.left) i

/-- Stage `n` of the compactly supported cohomology inverse system is
`H_c^i(X, F.stage n)`. -/
theorem cohomologyCompactSupportSystem_obj (F : ZEllSheaf X.left ℓ) (i n : ℕ) :
    (cohomologyCompactSupportSystem P F i).obj (op n) =
      stageCohomologyCompactSupport P F n i := sorry

/-- Compactly supported ℓ-adic cohomology `H_c^i(X, F)` of a `ℤ_[ℓ]`-sheaf, as the
inverse limit of the compactly supported étale cohomology of its stages. -/
def cohomologyCompactSupport (F : ZEllSheaf X.left ℓ) (i : ℕ) : AddCommGrpCat.{u} :=
  limit (cohomologyCompactSupportSystem P F i)

/-- Unfolding of compactly supported ℓ-adic cohomology as an inverse limit. -/
theorem cohomologyCompactSupport_eq (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    cohomologyCompactSupport P F i = limit (cohomologyCompactSupportSystem P F i) := sorry

/-- Projection from compactly supported ℓ-adic cohomology onto a stage. -/
def cohomologyCompactSupport_π (F : ZEllSheaf X.left ℓ) (i n : ℕ) :
    cohomologyCompactSupport P F i ⟶ stageCohomologyCompactSupport P F n i :=
  limit.π (cohomologyCompactSupportSystem P F i) (op n)

/-- Compactly supported ℓ-adic cohomology is the inverse limit of
`H_c^i(X, F.stage n)`, equivalently of the positively indexed stages
`H_c^i(X, F_{n+1})` for `n : ℕ`. -/
theorem cohomologyCompactSupport_spec (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    cohomologyCompactSupport P F i = limit (cohomologyCompactSupportSystem P F i) ∧
      ∀ n, (cohomologyCompactSupportSystem P F i).obj (op n) =
        stageCohomologyCompactSupport P F n i := sorry

/-- Compactly supported ℓ-adic cohomology is independent of the choice of
compactification, up to isomorphism. -/
theorem cohomologyCompactSupport_independent
    (Q : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι Q)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Compactification.Of.ι Q)).op.HasLeftKanExtension G]
    [HasWeakSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})]
    (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    Nonempty (cohomologyCompactSupport P F i ≅ cohomologyCompactSupport Q F i) := sorry

/-- Scalar-multiplication components by a `ℤ_[ℓ]`-integer on compactly supported
ℓ-adic cohomology. -/
def cohomologyCompactSupportSMulπ (F : ZEllSheaf X.left ℓ) (i : ℕ) (a : ℤ_[ℓ]) :
    (Functor.const ℕᵒᵖ).obj (cohomologyCompactSupport P F i) ⟶
      cohomologyCompactSupportSystem P F i where
  app n :=
    (PadicInt.toZModPow (n.unop + 1) a).val •
      limit.π (cohomologyCompactSupportSystem P F i) n
  naturality := sorry

/-- The cone presenting scalar multiplication on compactly supported ℓ-adic
cohomology. -/
def cohomologyCompactSupportSMulCone (F : ZEllSheaf X.left ℓ) (i : ℕ) (a : ℤ_[ℓ]) :
    Cone (cohomologyCompactSupportSystem P F i) where
  pt := cohomologyCompactSupport P F i
  π := cohomologyCompactSupportSMulπ P F i a

/-- The endomorphism of compactly supported ℓ-adic cohomology given by scalar
multiplication by a `ℤ_[ℓ]`-integer. -/
def cohomologyCompactSupportSMulHom (F : ZEllSheaf X.left ℓ) (i : ℕ) (a : ℤ_[ℓ]) :
    cohomologyCompactSupport P F i ⟶ cohomologyCompactSupport P F i :=
  limit.lift (cohomologyCompactSupportSystem P F i)
    (cohomologyCompactSupportSMulCone P F i a)

/-- The unit scalar acts as the identity on compactly supported ℓ-adic cohomology. -/
theorem cohomologyCompactSupportSMulHom_one_apply (F : ZEllSheaf X.left ℓ) (i : ℕ)
    (element : cohomologyCompactSupport P F i) :
    cohomologyCompactSupportSMulHom P F i 1 element = element := sorry

/-- Multiplication of scalars acts by successive scalar endomorphisms on compactly
supported ℓ-adic cohomology. -/
theorem cohomologyCompactSupportSMulHom_mul_apply (F : ZEllSheaf X.left ℓ) (i : ℕ)
    (a b : ℤ_[ℓ]) (element : cohomologyCompactSupport P F i) :
    cohomologyCompactSupportSMulHom P F i (a * b) element =
      cohomologyCompactSupportSMulHom P F i a
        (cohomologyCompactSupportSMulHom P F i b element) := sorry

/-- Addition of scalars acts by pointwise addition on compactly supported ℓ-adic cohomology. -/
theorem cohomologyCompactSupportSMulHom_add_apply (F : ZEllSheaf X.left ℓ) (i : ℕ)
    (a b : ℤ_[ℓ]) (element : cohomologyCompactSupport P F i) :
    cohomologyCompactSupportSMulHom P F i (a + b) element =
      cohomologyCompactSupportSMulHom P F i a element +
        cohomologyCompactSupportSMulHom P F i b element := sorry

/-- The zero scalar acts by zero on compactly supported ℓ-adic cohomology. -/
theorem cohomologyCompactSupportSMulHom_zero_apply (F : ZEllSheaf X.left ℓ) (i : ℕ)
    (element : cohomologyCompactSupport P F i) :
    cohomologyCompactSupportSMulHom P F i 0 element = 0 := sorry

/-- The `ℤ_[ℓ]`-module structure on compactly supported ℓ-adic cohomology. -/
@[implicit_reducible]
def cohomologyCompactSupportModuleStructure (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    Module ℤ_[ℓ] (cohomologyCompactSupport P F i) where
  smul a element := cohomologyCompactSupportSMulHom P F i a element
  one_smul := cohomologyCompactSupportSMulHom_one_apply P F i
  mul_smul := cohomologyCompactSupportSMulHom_mul_apply P F i
  smul_zero a := (cohomologyCompactSupportSMulHom P F i a).hom.map_zero
  smul_add a := (cohomologyCompactSupportSMulHom P F i a).hom.map_add
  add_smul := cohomologyCompactSupportSMulHom_add_apply P F i
  zero_smul := cohomologyCompactSupportSMulHom_zero_apply P F i

/-- Compactly supported ℓ-adic cohomology as a `ℤ_[ℓ]`-module. -/
def cohomologyCompactSupportModule (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    ModuleCat.{u} ℤ_[ℓ] :=
  @ModuleCat.of ℤ_[ℓ] _ (cohomologyCompactSupport P F i) _
    (cohomologyCompactSupportModuleStructure P F i)

/-- The underlying additive group of module-valued compactly supported ℓ-adic
cohomology is its inverse limit. -/
theorem cohomologyCompactSupportModule_eq (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    (forget₂ (ModuleCat.{u} ℤ_[ℓ]) AddCommGrpCat.{u}).obj
      (cohomologyCompactSupportModule P F i) = cohomologyCompactSupport P F i := sorry

/-- Compactly supported ℓ-adic cohomology with `ℚ_[ℓ]` coefficients of
`F' ⊗ ℚ_[ℓ]`, obtained by extending scalars from the `ℤ_[ℓ]`-cohomology of `F'`. -/
def cohomologyCompactSupportQEll (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    ModuleCat.{u} ℚ_[ℓ] :=
  (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
    (cohomologyCompactSupportModule P F i)

/-- Unfolding of `ℚ_[ℓ]`-coefficient compactly supported cohomology as extension of
scalars along `ℤ_[ℓ] →+* ℚ_[ℓ]`. -/
theorem cohomologyCompactSupportQEll_eq (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    cohomologyCompactSupportQEll P F i =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (cohomologyCompactSupportModule P F i) := sorry

/-- Compactly supported cohomology of `F' ⊗ ℚ_[ℓ]` is the scalar extension of
`H_c^i(X, F')` from `ℤ_[ℓ]` to `ℚ_[ℓ]`, and the underlying integral additive group
is the compactly supported inverse limit. -/
theorem cohomologyCompactSupportQEll_spec (F : ZEllSheaf X.left ℓ) (i : ℕ) :
    cohomologyCompactSupportQEll P F i =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (cohomologyCompactSupportModule P F i) ∧
      (forget₂ (ModuleCat.{u} ℤ_[ℓ]) AddCommGrpCat.{u}).obj
        (cohomologyCompactSupportModule P F i) = cohomologyCompactSupport P F i := sorry

end CompactSupport

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
