/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import ReasLib.RingTheory.Extension.Cotangent.ExtOne
public import ReasLib.RingTheory.RingHom.SquareZero.AlgebraExtension

/-!
# Polynomial lifts of square-zero algebra extensions

A polynomial presentation lifts through a square-zero algebra extension. Its
restriction to the presentation kernel induces a conormal map and an Ext¹ class.
-/

@[expose] public section

noncomputable section

universe u

open Algebra Algebra.Generators Algebra.Extension
open MvPolynomial

namespace RingHom.SquareZeroExtension

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- The A-algebra lift of a polynomial presentation through a square-zero
surjection, obtained by evaluating on a section of the surjection. -/
def presentationLift {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _) :
    -- Local instance justification (defeq pin): the solution's carrier ring is the dependent ring structure used by the lift's codomain.
    letI := S.commRing
    -- Local instance justification (defeq pin): the algebra structure induced by the specified A-algebra map is required by the typed lift result.
    letI : Algebra A S.carrier := S.fromA'.toAlgebra
    G.Ring →ₐ[A] S.carrier :=
  -- Local instance justification (defeq pin): the solution's carrier ring is the dependent ring structure used by evaluation.
  letI := S.commRing
  -- Local instance justification (defeq pin): the supplied square-zero structure is required to obtain the surjective section.
  letI := S.isSquareZero
  -- Local instance justification (defeq pin): evaluation must use the algebra structure induced by the specified A-algebra map.
  letI : Algebra A S.carrier := S.fromA'.toAlgebra
  MvPolynomial.aeval (Function.surjInv S.isSquareZero.surjective ∘ G.val)

/-- The lift recovers the original presentation after projection. -/
theorem presentationLift_comp {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _) :
    -- Local instance justification (defeq pin): the solution's carrier ring is the dependent ring structure in the projection identity.
    letI := S.commRing
    -- Local instance justification (defeq pin): the projection identity uses the supplied square-zero structure.
    letI := S.isSquareZero
    -- Local instance justification (defeq pin): the projection identity is typed over the algebra induced by S.fromA'.
    letI : Algebra A S.carrier := S.fromA'.toAlgebra
    S.toB.comp (presentationLift G S).toRingHom = algebraMap G.Ring B := sorry

/-- The lift sends each polynomial variable to a lift of the corresponding
generator. -/
theorem presentationLift_X {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _)
    (i : ι) :
    -- Local instance justification (defeq pin): the solution's carrier ring is the dependent ring structure in the generator identity.
    letI := S.commRing
    -- Local instance justification (defeq pin): the generator identity uses the supplied square-zero structure.
    letI := S.isSquareZero
    -- Local instance justification (defeq pin): the generator identity is typed over the algebra induced by S.fromA'.
    letI : Algebra A S.carrier := S.fromA'.toAlgebra
    S.toB (presentationLift G S (X i)) = G.val i := sorry

/-- The lift sends the presentation kernel into the square-zero kernel. -/
theorem presentationLift_mem_ker {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _)
    (j : G.toExtension.ker) :
    -- Local instance justification (defeq pin): the solution's carrier ring is the dependent ring structure in the kernel statement.
    letI := S.commRing
    -- Local instance justification (defeq pin): the kernel statement uses the supplied square-zero structure.
    letI := S.isSquareZero
    -- Local instance justification (defeq pin): the kernel statement is typed over the algebra induced by S.fromA'.
    letI : Algebra A S.carrier := S.fromA'.toAlgebra
    S.toB (presentationLift G S j.1) = 0 := sorry

/-- The restriction of the lifted presentation to its kernel, identified with N. -/
def restrictToKer {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _) :
    -- Local instance justification (defeq pin): the restriction codomain uses the solution's dependent carrier ring.
    letI := S.commRing
    -- Local instance justification (defeq pin): the restriction depends on the supplied square-zero structure.
    letI := S.isSquareZero
    -- Local instance justification (defeq pin): the restriction's scalar structure is induced by S.fromA'.
    letI : Algebra A S.carrier := S.fromA'.toAlgebra
    G.toExtension.ker →ₗ[A] N where
  toFun j :=
    -- Local instance justification (defeq pin): kernel evaluation uses the solution's dependent carrier ring.
    letI := S.commRing
    -- Local instance justification (defeq pin): kernel evaluation uses the supplied square-zero structure.
    letI := S.isSquareZero
    -- Local instance justification (defeq pin): kernel evaluation is typed over the algebra induced by S.fromA'.
    letI : Algebra A S.carrier := S.fromA'.toAlgebra
    let h : presentationLift G S j.1 ∈ RingHom.ker S.toB :=
      (mem_ker (f := S.toB) (r := presentationLift G S j.1)).mpr
        (presentationLift_mem_ker G S j)
    S.kernelEquiv (ofMem h)
  map_add' := sorry
  map_smul' := sorry

/-- The kernel restriction is represented by the lifted presentation element. -/
theorem restrictToKer_apply {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _)
    (j : G.toExtension.ker) :
    -- Local instance justification (defeq pin): the kernel equivalence is expressed using the solution's dependent carrier ring.
    letI := S.commRing
    -- Local instance justification (defeq pin): the kernel equivalence uses the supplied square-zero structure.
    letI := S.isSquareZero
    -- Local instance justification (defeq pin): the kernel equivalence is typed over the algebra induced by S.fromA'.
    letI : Algebra A S.carrier := S.fromA'.toAlgebra
    val (S.kernelEquiv.symm (restrictToKer G S j)) = presentationLift G S j.1 := sorry

/-- The induced B-linear map from the conormal module to N. -/
def conormalHom {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _) :
    G.toExtension.Cotangent →ₗ[B] N where
  toFun x := Ideal.Cotangent.lift (restrictToKer G S) sorry (Cotangent.val x)
  map_add' := sorry
  map_smul' := sorry

/-- The conormal map agrees with the kernel restriction on generators. -/
theorem conormalHom_mk {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _)
    (j : G.toExtension.ker) :
    conormalHom G S (Cotangent.mk j) = restrictToKer G S j := sorry

/-- The Ext¹ class induced by a square-zero extension and a presentation. -/
def conormalClass {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _) :
    extOneOf G N :=
  extOneOf_mk G N (conormalHom G S)

/-- The conormal class is represented by the conormal map. -/
theorem conormalClass_eq_mk {ι : Type u} (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _) :
    conormalClass G S = extOneOf_mk G N (conormalHom G S) := sorry

/-- The inverse classification map sends an extension to its conormal class. -/
theorem algebraExtensionEquiv_symm_eq_conormalClass {ι : Type u}
    (G : Algebra.Generators A B ι)
    (S : @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _) :
    (algebraExtensionEquiv A B N).symm (isoClassMk S) =
      compareToSelf G N (conormalClass G S) := sorry

end RingHom.SquareZeroExtension
