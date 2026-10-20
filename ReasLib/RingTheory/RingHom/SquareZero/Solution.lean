module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.Ideal.Cotangent
public import ReasLib.RingTheory.RingHom.LiftingSquare
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Solutions of a relative square-zero algebra extension

Given a square-zero surjection π : A' →+* A, an A-algebra B, a B-module N whose
A-action is restriction of scalars along A →+* B, and an A-linear map c from
ker π to N, a solution is a square-zero surjection B' →+* B together with a
B-linear identification of its kernel with N that induces c.
-/

@[expose] public section

noncomputable section

universe u

namespace RingHom
namespace SquareZeroExtension

variable {A' A : Type u} [CommRing A'] [CommRing A]

/-- The kernel of a square-zero extension, as a type synonym of `RingHom.ker`. -/
def KernelModule (π : A' →+* A) [π.IsSquareZeroExtension] : Type u :=
  ker π

/-- The kernel module of a square-zero extension is an abelian group. -/
instance instAddCommGroup_kernelModule (π : A' →+* A) [π.IsSquareZeroExtension] :
    AddCommGroup (KernelModule π) :=
  inferInstanceAs (AddCommGroup (ker π))

/-- The kernel of a square-zero extension is a module over the source ring. -/
instance instModule_source (π : A' →+* A) [π.IsSquareZeroExtension] :
    Module A' (KernelModule π) :=
  inferInstanceAs (Module A' (ker π))

/-- The underlying element of the source ring. -/
def val {π : A' →+* A} [π.IsSquareZeroExtension] (x : KernelModule π) : A' :=
  x.1

/-- Package an element of the kernel as a kernel-module element. -/
def ofMem {π : A' →+* A} [π.IsSquareZeroExtension] {x : A'} (hx : x ∈ ker π) :
    KernelModule π :=
  ⟨x, hx⟩

/-- Canonical identification of the kernel module with the kernel ideal. -/
def equivKer (π : A' →+* A) [π.IsSquareZeroExtension] :
    KernelModule π ≃ₗ[A'] ker π :=
  LinearEquiv.refl A' (KernelModule π)

/-- An element of the source ring lies in the kernel module iff it vanishes under π. -/
theorem mem_iff (π : A' →+* A) [π.IsSquareZeroExtension] {x : A'} :
    (∃ y : KernelModule π, val y = x) ↔ π x = 0 := sorry

/-- The cotangent of the kernel, as a module over the target via A' ⧸ ker π ≃+* A. -/
instance instModule_cotangent (π : A' →+* A) [hπ : π.IsSquareZeroExtension] :
    Module A (Ideal.Cotangent (ker π)) :=
  Module.compHom _
    (π.quotientKerEquivOfSurjective hπ.surjective).symm.toRingHom

/-- The source-linear identification of a square-zero kernel with its cotangent module. -/
def toCotangentEquiv_source (π : A' →+* A) [hπ : π.IsSquareZeroExtension] :
    KernelModule π ≃ₗ[A'] Ideal.Cotangent (ker π) :=
  LinearEquiv.ofBijective (Ideal.toCotangent (ker π))
    ⟨fun x y hxy =>
      Subtype.ext
        (sub_eq_zero.mp
          (Iff.mp (Submodule.mem_bot A')
            (Eq.subst (motive := fun I => x.1 - y.1 ∈ I) hπ.ker_sq_eq_bot
              ((Ideal.toCotangent_eq (I := ker π) (x := x) (y := y)).mp hxy)))),
      Ideal.toCotangent_surjective (ker π)⟩

/-- The kernel of a square-zero extension is a module over the target ring. -/
instance instModule_kernelModule (π : A' →+* A) [π.IsSquareZeroExtension] :
    Module A (KernelModule π) :=
  (toCotangentEquiv_source π).toAddEquiv.module A

/-- The target-linear identification of a square-zero kernel with its cotangent module. -/
def toCotangentEquiv (π : A' →+* A) [π.IsSquareZeroExtension] :
    KernelModule π ≃ₗ[A] Ideal.Cotangent (ker π) :=
  (toCotangentEquiv_source π).toAddEquiv.linearEquiv A

variable {B : Type u} [CommRing B] [Algebra A B]

/-- The structure morphism of the given `A`-algebra. -/
def structureMap : A →+* B :=
  (inferInstance : Algebra A B).algebraMap

variable (π : A' →+* A) [π.IsSquareZeroExtension]

/-- The map induced on kernels sends zero to zero. -/
private theorem kerMapOf_map_zero {Bprime : Type u} [CommRing Bprime] (fromA' : A' →+* Bprime)
    (toB : Bprime →+* B)
    (hcomm : toB.comp fromA' = (structureMap : A →+* B).comp π)
    [toB.IsSquareZeroExtension] : (fun x : KernelModule π =>
    ofMem
      (Iff.mpr (mem_ker (f := toB) (r := fromA' x.1))
        ((DFunLike.congr_fun hcomm x.1).trans
          ((congrArg (structureMap : A →+* B) x.2).trans
            (map_zero (structureMap : A →+* B)))))) 0 = 0 := sorry

/-- The map induced on kernels preserves addition. -/
private theorem kerMapOf_map_add {Bprime : Type u} [CommRing Bprime] (fromA' : A' →+* Bprime)
    (toB : Bprime →+* B)
    (hcomm : toB.comp fromA' = (structureMap : A →+* B).comp π)
    [toB.IsSquareZeroExtension] (x y : KernelModule π) :
    (fun x : KernelModule π =>
    ofMem
      (Iff.mpr (mem_ker (f := toB) (r := fromA' x.1))
        ((DFunLike.congr_fun hcomm x.1).trans
          ((congrArg (structureMap : A →+* B) x.2).trans
            (map_zero (structureMap : A →+* B)))))) (x + y) =
      (fun x : KernelModule π =>
    ofMem
      (Iff.mpr (mem_ker (f := toB) (r := fromA' x.1))
        ((DFunLike.congr_fun hcomm x.1).trans
          ((congrArg (structureMap : A →+* B) x.2).trans
            (map_zero (structureMap : A →+* B)))))) x + (fun x : KernelModule π =>
    ofMem
      (Iff.mpr (mem_ker (f := toB) (r := fromA' x.1))
        ((DFunLike.congr_fun hcomm x.1).trans
          ((congrArg (structureMap : A →+* B) x.2).trans
            (map_zero (structureMap : A →+* B)))))) y := sorry

/-- The map on kernels induced by a commutative square of ring homomorphisms. -/
def kerMapOf {Bprime : Type u} [CommRing Bprime] (fromA' : A' →+* Bprime)
    (toB : Bprime →+* B)
    (hcomm : toB.comp fromA' = (structureMap : A →+* B).comp π)
    [toB.IsSquareZeroExtension] : KernelModule π →+ KernelModule toB where
  toFun := (fun x : KernelModule π =>
    ofMem
      (Iff.mpr (mem_ker (f := toB) (r := fromA' x.1))
        ((DFunLike.congr_fun hcomm x.1).trans
          ((congrArg (structureMap : A →+* B) x.2).trans
            (map_zero (structureMap : A →+* B))))))
  map_zero' := by exact kerMapOf_map_zero π fromA' toB hcomm
  map_add' := by exact kerMapOf_map_add π fromA' toB hcomm

variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N]
variable (c : KernelModule π →ₗ[A] N)

/-- A solution of the relative square-zero extension problem: a square-zero
surjection B' →+* B whose kernel is identified with N and which induces c.
The A-action on N is restriction along A →+* B. -/
structure Solution [IsScalarTower A B N] where
  /-- The unknown middle ring B'. -/
  carrier : Type u
  /-- Commutative ring structure on the middle term. -/
  [commRing : CommRing carrier]
  /-- The structure map A' →+* B'. -/
  fromA' : A' →+* carrier
  /-- The square-zero surjection B' →+* B. -/
  toB : carrier →+* B
  /-- The right-hand square commutes. -/
  comm_right : toB.comp fromA' = (structureMap : A →+* B).comp π
  /-- The projection B' →+* B is a square-zero extension. -/
  [isSquareZero : toB.IsSquareZeroExtension]
  /-- B-linear identification of ker(B' →+* B) with N. -/
  kernelEquiv : KernelModule toB ≃ₗ[B] N
  /-- The induced map on kernels equals c. -/
  induces : ∀ x : KernelModule π,
    kernelEquiv (kerMapOf π fromA' toB comm_right x) = c x

namespace Solution

/-- Assemble a solution from a middle ring, its structure maps, a kernel
identification, and the induced-map condition. -/
def of [IsScalarTower A B N] {Bprime : Type u} [CommRing Bprime]
    (fromA' : A' →+* Bprime) (toB : Bprime →+* B)
    [hsq : toB.IsSquareZeroExtension]
    (comm_right : toB.comp fromA' = (structureMap : A →+* B).comp π)
    (kernelEquiv : KernelModule toB ≃ₗ[B] N)
    (induces : ∀ x : KernelModule π,
      kernelEquiv (kerMapOf π fromA' toB comm_right x) = c x) :
    Solution (B := B) (N := N) π c where
  carrier := Bprime
  commRing := inferInstance
  fromA' := fromA'
  toB := toB
  comm_right := comm_right
  isSquareZero := hsq
  kernelEquiv := kernelEquiv
  induces := induces

/-- The right-hand square of a solution commutes. -/
theorem spec [IsScalarTower A B N] (S : Solution (B := B) (N := N) π c) :
    S.toB.comp S.fromA' = (structureMap : A →+* B).comp π := sorry

/-- The kernel map of a solution preserves addition. -/
private theorem kerMap_map_add [IsScalarTower A B N] (S : Solution (B := B) (N := N) π c)
    (x y : KernelModule π) :
    -- Local instance justification (proof-local temporary data): unpack the stored ring of the explicit solution.
    letI := S.commRing
    -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
    letI := S.isSquareZero
    -- Local instance justification (search instability): the intermediate ring B is not determined by the kernel type.
    letI : Module A (KernelModule S.toB) := Module.compHom _ (structureMap : A →+* B)
    kerMapOf π S.fromA' S.toB S.comm_right (x + y) =
      kerMapOf π S.fromA' S.toB S.comm_right x + kerMapOf π S.fromA' S.toB S.comm_right y := sorry

/-- The kernel map of a solution respects the base-ring scalar action. -/
private theorem kerMap_map_smul [IsScalarTower A B N] (S : Solution (B := B) (N := N) π c)
    (r : A) (x : KernelModule π) :
    -- Local instance justification (proof-local temporary data): unpack the stored ring of the explicit solution.
    letI := S.commRing
    -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
    letI := S.isSquareZero
    -- Local instance justification (search instability): the intermediate ring B is not determined by the kernel type.
    letI : Module A (KernelModule S.toB) := Module.compHom _ (structureMap : A →+* B)
    kerMapOf π S.fromA' S.toB S.comm_right (r • x) =
      r • kerMapOf π S.fromA' S.toB S.comm_right x := sorry

/-- The A-linear map on kernels induced by a solution. -/
def kerMap [IsScalarTower A B N] (S : Solution (B := B) (N := N) π c) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
    letI := S.isSquareZero
    -- Local instance justification (search instability): restrict-scalars along Algebra A B cannot infer the intermediate ring B from KernelModule S.toB.
    letI : Module A (KernelModule S.toB) :=
      Module.compHom _ (structureMap : A →+* B)
    KernelModule π →ₗ[A] KernelModule S.toB :=
  -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
  letI := S.isSquareZero
  -- Local instance justification (search instability): restrict-scalars along Algebra A B cannot infer the intermediate ring B from KernelModule S.toB.
  letI : Module A (KernelModule S.toB) :=
    Module.compHom _ (structureMap : A →+* B)
  { toFun := fun x => kerMapOf π S.fromA' S.toB S.comm_right x
    map_add' := by exact kerMap_map_add π c S
    map_smul' := by exact kerMap_map_smul π c S }

/-- `kerMapOf` acts by the structure map A' →+* B'. -/
theorem kerMapOf_apply {Bprime : Type u} [CommRing Bprime] (fromA' : A' →+* Bprime)
    (toB : Bprime →+* B) (hcomm : toB.comp fromA' = (structureMap : A →+* B).comp π)
    [toB.IsSquareZeroExtension] (x : KernelModule π) :
    val (kerMapOf π fromA' toB hcomm x) = fromA' (val x) := sorry

/-- The inclusion determined by the coefficient identification sends zero to zero. -/
private theorem inclusion_map_zero [IsScalarTower A B N] (S : Solution (B := B) (N := N) π c) :
    -- Local instance justification (proof-local temporary data): unpack the stored ring of the explicit solution.
    letI := S.commRing
    -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
    letI := S.isSquareZero
    val (S.kernelEquiv.symm 0) = 0 := sorry

/-- The inclusion determined by the coefficient identification preserves addition. -/
private theorem inclusion_map_add [IsScalarTower A B N] (S : Solution (B := B) (N := N) π c)
    (x y : N) :
    -- Local instance justification (proof-local temporary data): unpack the stored ring of the explicit solution.
    letI := S.commRing
    -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
    letI := S.isSquareZero
    val (S.kernelEquiv.symm (x + y)) = val (S.kernelEquiv.symm x) + val (S.kernelEquiv.symm y) := sorry

/-- The additive inclusion of N into the middle ring of a solution. -/
def inclusion [IsScalarTower A B N] (S : Solution (B := B) (N := N) π c) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
    letI := S.isSquareZero
    N →+ S.carrier :=
  -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
  letI := S.commRing
  -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
  letI := S.isSquareZero
  { toFun := fun n => val (S.kernelEquiv.symm n)
    map_zero' := by exact inclusion_map_zero π c S
    map_add' := by exact inclusion_map_add π c S }

/-- The identification of kernels induces the given map c. -/
theorem induces_eq [IsScalarTower A B N] (S : Solution (B := B) (N := N) π c)
    (x : KernelModule π) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    -- Local instance justification (proof-local temporary data): bundled `S.isSquareZero` is not globally registered on the structure Solution.
    letI := S.isSquareZero
    S.kernelEquiv (kerMapOf π S.fromA' S.toB S.comm_right x) = c x := sorry

/-- The right-hand commutative square of a solution, as a lifting square. -/
def toLiftingSquare [IsScalarTower A B N] (S : Solution (B := B) (N := N) π c) :
    -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
    letI := S.commRing
    LiftingSquare π S.toB :=
  -- Local instance justification (proof-local temporary data): bundled `S.commRing` is not globally registered on the structure Solution.
  letI := S.commRing
  { upper := S.fromA'
    lower := (structureMap : A →+* B)
    comm := S.comm_right }

/-- The bottom row 0 ⟶ ker π ⟶ A' ⟶ A is exact at A'. -/
theorem exact_bottom :
    Set.range (val : KernelModule π → A') = (ker π : Set A') := sorry

end Solution

end SquareZeroExtension
end RingHom

