/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import ReasLib.RingTheory.RingHom.SquareZero.Solution

/-!
# Split square-zero extensions

This file records the canonical split square-zero extension and the associated
identity-diagram solution used as a basepoint for extension classes.
-/

@[expose] public section

noncomputable section

universe u

open TrivSqZeroExt

namespace RingHom.SquareZeroExtension

/-- The identity map of a commutative ring is a square-zero extension. -/
instance instIsSquareZeroExtension_id (A : Type u) [CommRing A] :
    (RingHom.id A).IsSquareZeroExtension := sorry

/-- The opposite scalar action induced by a commutative ring action. -/
@[reducible] def moduleMulOpposite (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] : Module Rᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id R).fromOpposite fun x y ↦ mul_comm x y)

/-- Opposite and ordinary scalar multiplication agree for a commutative ring. -/
theorem moduleMulOpposite_smul_eq_smul (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] (r : R) (x : M) :
    -- Local instance justification (instance diamond): opposite-module action is local to this equality; a global `Module Rᵐᵒᵖ M` instance diamonds.
    letI := moduleMulOpposite R M
    MulOpposite.op r • x = r • x := sorry

/-- The opposite scalar action is central for a commutative ring. -/
theorem isCentralScalar_of_commRing (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] :
    -- Local instance justification (instance diamond): opposite-module action is local to this centrality witness; a global `Module Rᵐᵒᵖ M` instance diamonds.
    letI := moduleMulOpposite R M
    IsCentralScalar R M := sorry

/-- The canonical projection from a trivial square-zero extension to its ring factor. -/
theorem trivFstRingHom_apply (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]
    [Module Bᵐᵒᵖ N] [IsCentralScalar B N] (x : TrivSqZeroExt B N) :
    (TrivSqZeroExt.fstHom B B N).toRingHom x = TrivSqZeroExt.fst x := sorry

/-- The canonical projection of a trivial square-zero extension is square-zero. -/
instance instIsSquareZeroExtension_trivFstRingHom (B N : Type u) [CommRing B]
    [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N] :
    (TrivSqZeroExt.fstHom B B N).toRingHom.IsSquareZeroExtension := sorry

set_option backward.privateInPublic true in
/-- An element inserted into a trivial square-zero extension lies in the projection kernel. -/
private theorem kernelInr_mem (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]
    [Module Bᵐᵒᵖ N] [IsCentralScalar B N] (n : N) :
    TrivSqZeroExt.inr n ∈ RingHom.ker (TrivSqZeroExt.fstHom B B N).toRingHom := sorry

set_option backward.privateInPublic true in
/-- The second projection followed by the kernel inclusion is the identity on the kernel. -/
private theorem kernelFst_left_inv (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]
    [Module Bᵐᵒᵖ N] [IsCentralScalar B N]
    (x : KernelModule (TrivSqZeroExt.fstHom B B N).toRingHom) :
    ofMem (kernelInr_mem B N (TrivSqZeroExt.snd (val x))) = x := sorry

set_option backward.privateInPublic true in
/-- The kernel inclusion followed by the second projection is the identity on the module. -/
private theorem kernelFst_right_inv (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]
    [Module Bᵐᵒᵖ N] [IsCentralScalar B N] (n : N) :
    TrivSqZeroExt.snd
        (val (ofMem (kernelInr_mem B N n) : KernelModule (TrivSqZeroExt.fstHom B B N).toRingHom)) = n := sorry

set_option backward.privateInPublic true in
/-- The second projection is additive on the projection kernel. -/
private theorem kernelFst_map_add (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]
    [Module Bᵐᵒᵖ N] [IsCentralScalar B N]
    (x y : KernelModule (TrivSqZeroExt.fstHom B B N).toRingHom) :
    TrivSqZeroExt.snd (val (x + y)) = TrivSqZeroExt.snd (val x) + TrivSqZeroExt.snd (val y) := sorry

set_option backward.privateInPublic true in
/-- The second projection is `B`-linear on the projection kernel. -/
private theorem kernelFst_map_smul (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]
    [Module Bᵐᵒᵖ N] [IsCentralScalar B N] (b : B)
    (x : KernelModule (TrivSqZeroExt.fstHom B B N).toRingHom) :
    TrivSqZeroExt.snd (val (b • x)) = b • TrivSqZeroExt.snd (val x) := sorry

set_option backward.privateInPublic true in
/-- The kernel of the canonical projection is identified with the module factor. -/
def kernelEquiv_fst (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]
    [Module Bᵐᵒᵖ N] [IsCentralScalar B N] :
    KernelModule (TrivSqZeroExt.fstHom B B N).toRingHom ≃ₗ[B] N where
  toFun x := TrivSqZeroExt.snd (val x)
  invFun n := ofMem (kernelInr_mem B N n)
  left_inv := kernelFst_left_inv B N
  right_inv := kernelFst_right_inv B N
  map_add' := kernelFst_map_add B N
  map_smul' := kernelFst_map_smul B N

/-- The forward computation rule for the kernel identification. -/
theorem kernelEquiv_fst_apply (B N : Type u) [CommRing B] [AddCommGroup N]
    [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N]
    (x : KernelModule (TrivSqZeroExt.fstHom B B N).toRingHom) :
    kernelEquiv_fst B N x = TrivSqZeroExt.snd (val x) := rfl

/-- The inverse computation rule for the kernel identification. -/
theorem kernelEquiv_fst_symm_val (B N : Type u) [CommRing B] [AddCommGroup N]
    [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N] (n : N) :
    val ((kernelEquiv_fst B N).symm n) = TrivSqZeroExt.inr n := sorry

/-- The zero coefficient map for the identity square-zero diagram. -/
def zeroKernelMap (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] :
    KernelModule (RingHom.id A) →ₗ[A] N :=
  0

/-- The zero coefficient map vanishes on every kernel element. -/
theorem zeroKernelMap_apply (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    (x : KernelModule (RingHom.id A)) :
    zeroKernelMap A B N x = 0 := sorry

/-- The coefficient map for the identity diagram is the zero linear map. -/
theorem zeroKernelMap_eq_zero (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] :
    zeroKernelMap A B N = 0 := sorry

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

set_option backward.privateInPublic true in
/-- The structure maps of the split identity-diagram extension commute. -/
private theorem trivialSolution_comm :
    -- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `Module Bᵐᵒᵖ N`; a global opposite-module instance on raw types diamonds.
    letI := moduleMulOpposite B N
    -- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `IsCentralScalar B N`; a global centrality instance on raw types diamonds.
    letI := isCentralScalar_of_commRing B N
    (TrivSqZeroExt.fstHom B B N).toRingHom.comp
        ((inlHom B N).comp (algebraMap A B)) =
      (structureMap : A →+* B).comp (RingHom.id A) := sorry

set_option backward.privateInPublic true in
/-- The split solution induces the zero coefficient map on the identity kernel. -/
private theorem trivialSolution_induces :
    -- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `Module Bᵐᵒᵖ N`; a global opposite-module instance on raw types diamonds.
    letI := moduleMulOpposite B N
    -- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `IsCentralScalar B N`; a global centrality instance on raw types diamonds.
    letI := isCentralScalar_of_commRing B N
    ∀ x : KernelModule (RingHom.id A),
      kernelEquiv_fst B N
          (kerMapOf (RingHom.id A) ((inlHom B N).comp (algebraMap A B))
            (TrivSqZeroExt.fstHom B B N).toRingHom (trivialSolution_comm A B N) x) =
        zeroKernelMap A B N x := sorry

set_option backward.privateInPublic true in
/-- The split solution of the identity diagram, with middle ring `TrivSqZeroExt B N`. -/
def trivialSolution :
    Solution (B := B) (N := N) (RingHom.id A) (zeroKernelMap A B N) :=
  -- Local instance justification (instance diamond): the split ring must use this selected opposite action; a global instance would compete with explicit opposite actions.
  letI := moduleMulOpposite B N
  -- Local instance justification (defeq pin): centrality certifies this selected opposite action and pins the split commutative-ring structure used by the solution and its computation lemmas.
  letI := isCentralScalar_of_commRing B N
  Solution.of (RingHom.id A) (zeroKernelMap A B N)
    ((inlHom B N).comp (algebraMap A B)) (TrivSqZeroExt.fstHom B B N).toRingHom
    (trivialSolution_comm A B N) (kernelEquiv_fst B N) (trivialSolution_induces A B N)

/-- The carrier of the split solution is the trivial square-zero extension. -/
theorem trivialSolution_carrier :
    (trivialSolution A B N).carrier = TrivSqZeroExt B N := rfl

/-- The structure map of the split solution is induced by `inlHom`. -/
theorem trivialSolution_fromA' :
    -- Local instance justification (defeq pin): `inlHom` must use the same selected opposite action as `trivialSolution` for the structure-map computation to hold definitionally.
    letI := moduleMulOpposite B N
    -- Local instance justification (defeq pin): centrality certifies that action and pins the split commutative-ring structure selected by `trivialSolution` for the displayed structure map.
    letI := isCentralScalar_of_commRing B N
    (trivialSolution A B N).fromA' = (inlHom B N).comp (algebraMap A B) := rfl

/-- The projection of the split solution is the canonical first projection. -/
theorem trivialSolution_toB :
    -- Local instance justification (defeq pin): `fstHom` must use the same selected opposite action as `trivialSolution` for the projection computation to hold definitionally.
    letI := moduleMulOpposite B N
    -- Local instance justification (defeq pin): centrality certifies that action and pins the split commutative-ring structure shared by the solution projection and `fstHom`.
    letI := isCentralScalar_of_commRing B N
    (trivialSolution A B N).toB = (TrivSqZeroExt.fstHom B B N).toRingHom := rfl

end SquareZeroExtension

end RingHom
