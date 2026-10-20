module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.RingTheory.RingHom.SquareZero.Diagram
public import ReasLib.RingTheory.RingHom.SquareZero.Split

/-!
# Pushout of a square-zero A-algebra extension along a coefficient map

Given 0 → M → B' → B → 0 and c : M →ₗ[B] N, the coefficient pushout constructs
B'_1 = (N × B')/M with M antidiagonally embedded, as a square-zero
A-algebra extension of B by N.
-/

@[expose] public section

noncomputable section

universe u

open TrivSqZeroExt

namespace RingHom.SquareZeroExtension

variable {A B M N : Type u}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

-- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `Module Bᵐᵒᵖ N`; a global opposite-module instance on raw types diamonds.
local instance : Module Bᵐᵒᵖ N := moduleMulOpposite B N
-- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `IsCentralScalar B N`; a global centrality instance on raw types diamonds.
local instance : IsCentralScalar B N := isCentralScalar_of_commRing B N

/-- The ring N × B' as the fibre product of `(TrivSqZeroExt.fstHom B B N).toRingHom` and B' → B. -/
def pushoutProduct
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    Subring (TrivSqZeroExt B N × SB.carrier) :=
  -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
  letI := SB.commRing
  (TrivSqZeroExt.fstHom B B N).toRingHom.pullback SB.toB

/-- Membership in `pushoutProduct` is the fibre-product condition on N ⊕ B and B'. -/
theorem mem_pushoutProduct
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M))
    {x :
      -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
      letI := SB.commRing
      TrivSqZeroExt B N × SB.carrier} :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    x ∈ pushoutProduct (N := N) SB ↔ (TrivSqZeroExt.fstHom B B N).toRingHom x.1 = SB.toB x.2 := sorry

/-- The antidiagonal generator (inr (c m), -inclusion m) of M in N × B'. -/
def pushoutAntidiagonalGen (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) (m : M) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    -- Local instance justification (defeq pin): kernel modules must use the supplied `SB.isSquareZero`.
    letI := SB.isSquareZero
    pushoutProduct (N := N) SB :=
  -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
  letI := SB.commRing
  -- Local instance justification (defeq pin): kernel modules must use the supplied `SB.isSquareZero`.
  letI := SB.isSquareZero
  ⟨(inr (c m), -Solution.inclusion (RingHom.id A) (zeroKernelMap A B M) SB m), sorry⟩

/-- The antidiagonal generator is the pair (inr (c m), -inclusion m). -/
theorem pushoutAntidiagonalGen_apply (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) (m : M) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    -- Local instance justification (defeq pin): kernel modules must use the supplied `SB.isSquareZero`.
    letI := SB.isSquareZero
    (pushoutAntidiagonalGen c SB m).1 =
      (inr (c m), -Solution.inclusion (RingHom.id A) (zeroKernelMap A B M) SB m) := sorry

/-- The antidiagonal ideal of M in N × B'. -/
def pushoutAntidiagonal (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    -- Local instance justification (defeq pin): kernel modules must use the supplied `SB.isSquareZero`.
    letI := SB.isSquareZero
    Ideal (pushoutProduct (N := N) SB) :=
  -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
  letI := SB.commRing
  -- Local instance justification (defeq pin): kernel modules must use the supplied `SB.isSquareZero`.
  letI := SB.isSquareZero
  Ideal.span (Set.range (pushoutAntidiagonalGen c SB))

/-- An element belongs to the antidiagonal ideal exactly when it is an
antidiagonal generator, so the ideal is the antidiagonal image of the coefficient module. -/
theorem mem_pushoutAntidiagonal_iff (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M))
    (x :
      -- Local instance justification (defeq pin): the fibre product uses the supplied SB.commRing.
      letI := SB.commRing
      pushoutProduct (N := N) SB) :
    -- Local instance justification (defeq pin): ideal membership uses the supplied SB.commRing.
    letI := SB.commRing
    -- Local instance justification (defeq pin): the antidiagonal inclusion uses the supplied SB.isSquareZero.
    letI := SB.isSquareZero
    x ∈ pushoutAntidiagonal c SB ↔ ∃ m : M, pushoutAntidiagonalGen c SB m = x := sorry

/-- The class of `(inr n, 0)` in N × B'. -/
def pushoutInr (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) (n : N) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    pushoutProduct (N := N) SB :=
  -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
  letI := SB.commRing
  ⟨(inr n, 0), sorry⟩

/-- `pushoutInr n` is the pair `(inr n, 0)`. -/
theorem pushoutInr_apply (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) (n : N) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    (pushoutInr c SB n).1 = (inr n, 0) := sorry

/-- Pushout of 0 → M → B' → B → 0 along c : M →ₗ[B] N, as a square-zero
A-algebra extension of B by N. The middle ring is (N × B')/M. -/
def pushoutAlong (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) :
    Solution (B := B) (N := N) (RingHom.id A) (zeroKernelMap A B N) :=
  -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
  letI := SB.commRing
  -- Local instance justification (defeq pin): kernel modules must use the supplied `SB.isSquareZero`.
  letI := SB.isSquareZero
  let fromA' :=
    (Ideal.Quotient.mk (pushoutAntidiagonal c SB)).comp
      (RingHom.codRestrict
        (RingHom.prod ((inlHom B N).comp (algebraMap A B)) SB.fromA')
        (pushoutProduct (N := N) SB) (fun _ ↦ sorry))
  let toB :=
    Ideal.Quotient.lift (pushoutAntidiagonal c SB)
      (SB.toB.comp (RingHom.pullbackSnd (TrivSqZeroExt.fstHom B B N).toRingHom SB.toB)) sorry
  -- Local instance justification (defeq pin): the explicitly specified quotient projection carries the square-zero laws required by Solution.of.
  letI : toB.IsSquareZeroExtension := ⟨sorry, sorry⟩
  Solution.of (RingHom.id A) (zeroKernelMap A B N) fromA' toB sorry
    { toFun := fun x ↦
        let r := Quotient.out x.1
        TrivSqZeroExt.snd r.1.1 + c (SB.kernelEquiv (ofMem (x := r.1.2) sorry))
      invFun := fun n ↦
        ofMem (x := Ideal.Quotient.mk (pushoutAntidiagonal c SB) (pushoutInr c SB n)) sorry
      left_inv := sorry
      right_inv := sorry
      map_add' := sorry
      map_smul' := sorry }
    sorry

/-- The projection B'_1 → B is the quotient lift of B' → B on the fibre product. -/
theorem pushoutAlong_toB (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    -- Local instance justification (defeq pin): kernel modules must use the supplied `SB.isSquareZero`.
    letI := SB.isSquareZero
    (pushoutAlong c SB).toB.comp (Ideal.Quotient.mk (pushoutAntidiagonal c SB)) =
      SB.toB.comp (RingHom.pullbackSnd (TrivSqZeroExt.fstHom B B N).toRingHom SB.toB) := sorry

/-- The inverse kernel identification sends n to the class of (inr n, 0). -/
theorem pushoutAlong_kernelEquiv_symm (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) (n : N) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    -- Local instance justification (defeq pin): kernel modules must use the supplied `SB.isSquareZero`.
    letI := SB.isSquareZero
    -- Local instance justification (defeq pin): quotient maps use the carrier ring supplied by the pushout solution.
    letI := (pushoutAlong c SB).commRing
    -- Local instance justification (defeq pin): the kernel identification uses the pushout solution’s square-zero structure.
    letI := (pushoutAlong c SB).isSquareZero
    val ((pushoutAlong c SB).kernelEquiv.symm n) =
      Ideal.Quotient.mk (pushoutAntidiagonal c SB) (pushoutInr c SB n) := sorry

/-- The identity-base connecting diagram from B' to the pushout along c. -/
def pushoutAlongDiagram (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) :
    RelativeDiagram SB (pushoutAlong c SB) where
  t' := RingHom.id A
  t := RingHom.id A
  g := RingHom.id B
  ν := c.toAddMonoidHom
  map_smul_ν := sorry
  comm_base := sorry
  comm_alg := sorry
  comm_kernel := sorry

/-- `pushoutAlongDiagram` has identity maps on A and B, and ν = c. -/
theorem pushoutAlongDiagram_spec (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) :
    (pushoutAlongDiagram c SB).t' = RingHom.id A ∧
      (pushoutAlongDiagram c SB).t = RingHom.id A ∧
      (pushoutAlongDiagram c SB).g = RingHom.id B ∧
      (pushoutAlongDiagram c SB).ν = c.toAddMonoidHom := sorry

/-- The canonical map from an extension to its coefficient pushout. -/
def toPushoutAlong (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) :
    FittingMap (pushoutAlongDiagram c SB) :=
  -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
  letI := SB.commRing
  -- Local instance justification (defeq pin): kernel modules must use the supplied `SB.isSquareZero`.
  letI := SB.isSquareZero
  -- Local instance justification (defeq pin): quotient maps use the carrier ring supplied by the pushout solution.
  letI := (pushoutAlong c SB).commRing
  FittingMap.of (pushoutAlongDiagram c SB)
    ((Ideal.Quotient.mk (pushoutAntidiagonal c SB)).comp
      (RingHom.codRestrict
        (RingHom.prod ((inlHom B N).comp SB.toB) (RingHom.id SB.carrier))
        (pushoutProduct (N := N) SB) (fun _ ↦ sorry)))
    sorry sorry sorry

/-- `toPushoutAlong` is compatible with the projections to B and the maps from A. -/
theorem toPushoutAlong_spec (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SB.commRing`.
    letI := SB.commRing
    -- Local instance justification (defeq pin): quotient maps use the carrier ring supplied by the pushout solution.
    letI := (pushoutAlong c SB).commRing
    (pushoutAlong c SB).toB.comp (toPushoutAlong c SB).hom = SB.toB ∧
      (toPushoutAlong c SB).hom.comp SB.fromA' = (pushoutAlong c SB).fromA' := sorry

end SquareZeroExtension

end RingHom
