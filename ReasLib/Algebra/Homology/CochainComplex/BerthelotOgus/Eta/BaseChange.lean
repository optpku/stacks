module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.Flat.TorsionFree
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta

/-!
# Flat base change for the Berthelot-Ogus eta operator

Flat scalar extension preserves regular scalar actions degreewise.  Consequently it preserves the
termwise torsion-freeness needed by the eta construction, and the eta operator commutes with flat
base change on nonnegative cochain complexes.
@stack 0GSR
-/

@[expose] public section

open CategoryTheory
open scoped BerthelotOgus nonZeroDivisors

universe u v w

namespace Module.Flat

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- A nonzerodivisor remains a nonzerodivisor after extension along a flat algebra.  This is the
ring-valued form of `Module.Flat.isSMulRegular_of_nonZeroDivisors`, transported along
`isSMulRegular_algebraMap_iff`. -/
@[stacks 0GSR "nonzerodivisors under flat base change"]
theorem algebraMap_mem_nonZeroDivisors [Flat A B] (f : A) (hf : f ∈ nonZeroDivisors A) :
    algebraMap A B f ∈ nonZeroDivisors B := sorry

end Module.Flat

namespace CochainComplex.BerthelotOgus.Nat

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Flat extension of scalars preserves termwise torsion-freeness of a nonnegative cochain
complex. -/
@[stacks 0GSR "termwise torsion-freeness under flat base change"]
theorem IsTermwiseTorsionFree.extendScalars [Module.Flat A B] {f : A}
    {K : CochainComplex (ModuleCat.{max v w} A) ℕ} (hK : IsTermwiseTorsionFree f K) :
    IsTermwiseTorsionFree (algebraMap A B f)
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) := sorry

namespace BaseChange

/-- The ambient degree map from the scalar extension of an eta term to the scalar extension of
the original term.  It is scalar extension of the defining subtype inclusion. -/
noncomputable def inclusionLinear
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
        (ModuleCat.of A (term f K n)) →ₗ[B]
      (ModuleCat.extendScalars (algebraMap A B)).obj (K.X n) :=
  ((ModuleCat.extendScalars (algebraMap A B)).map
    (ModuleCat.ofHom (term f K n).subtype)).hom

/-- The ambient scalar-extension map sends the scalar extension of an eta term into the eta term
of the scalar-extended complex. -/
theorem inclusion_mem (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ)
    (x : (ModuleCat.extendScalars (algebraMap A B)).obj
      (ModuleCat.of A (term f K n))) :
    inclusionLinear (B := B) f K n x ∈
      term (algebraMap A B f)
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) n := sorry

/-- The degree map from the scalar extension of `η[f] K` to `η[algebraMap A B f]` of the
scalar-extended complex. -/
noncomputable def termLinear
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
        (ModuleCat.of A (term f K n)) →ₗ[B]
      term (algebraMap A B f)
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) n :=
  (inclusionLinear (B := B) f K n).codRestrict _ (inclusion_mem (B := B) f K n)

/-- The bundled degree map from the scalar extension of `η[f] K` to the eta term of the
scalar-extended complex. -/
noncomputable def termHom
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (η[f] K)).X n ⟶
      (η[algebraMap A B f]
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K)).X n :=
  ConcreteCategory.ofHom (C := ModuleCat B) (termLinear (B := B) f K n)

/-- The underlying linear map of the bundled degree comparison is `termLinear`. -/
@[simp]
theorem termHom_hom
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (termHom (B := B) f K n).hom = termLinear (B := B) f K n := sorry

/-- The degreewise flat-base-change maps commute with the eta differentials. -/
theorem termLinear_comm (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    termHom (B := B) f K i ≫
        (η[algebraMap A B f]
          (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K)).d i j =
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (η[f] K)).d i j ≫
        termHom (B := B) f K j := sorry

/-- The canonical map from the scalar extension of `η[f] K` to the eta complex of the
scalar-extended complex. -/
@[stacks 0GSR "Berthelot-Ogus eta flat-base-change comparison"]
noncomputable def comparison (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) :
    ((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (η[f] K) ⟶
      η[algebraMap A B f]
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) where
  f n := termHom (B := B) f K n
  comm' i j hij := termLinear_comm (B := B) f K i j hij

/-- The component of the eta base-change comparison is the canonical degree comparison. -/
@[simp]
theorem comparison_f
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℕ) (n : ℕ) :
    (comparison (B := B) f K).f n = termHom (B := B) f K n := sorry

/-- For a flat algebra, the canonical base-change comparison for the eta operator is an
isomorphism.  The inverse remains encapsulated by `IsIso`; no chosen inverse is part of this API. -/
@[stacks 0GSR "Berthelot-Ogus eta commutes with flat base change"]
instance comparisonIsIso [Module.Flat A B] (f : A)
    (K : CochainComplex (ModuleCat.{max v w} A) ℕ) :
    IsIso (comparison (B := B) f K) := sorry

end BaseChange

end CochainComplex.BerthelotOgus.Nat
