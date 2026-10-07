module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import stacks_project.Chap91.Lemma_91_2_1_Diagram
public import stacks_project.Chap91.Lemma_91_2_3_Trivial

/-!
# Pushout of a square-zero A-algebra extension along a coefficient map

Given 0 → M → B' → B → 0 and c : M →ₗ[B] N, the source constructs
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

/-- The ring N × B' as the fibre product of `trivFstRingHom B N` and B' → B. -/
def pushoutProduct (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    Subring (TrivSqZeroExt B N × SB.carrier) :=
  -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
  letI := SB.commRing
  let _ := c
  (trivFstRingHom B N).pullback SB.toB

/-- Membership in `pushoutProduct` is the fibre-product condition on N ⊕ B and B'. -/
theorem mem_pushoutProduct (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _)
    {x :
      -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
      letI := SB.commRing
      TrivSqZeroExt B N × SB.carrier} :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    x ∈ pushoutProduct c SB ↔ trivFstRingHom B N x.1 = SB.toB x.2 := sorry

/-- The antidiagonal generator (inr (c m), -inclusion m) of M in N × B'. -/
def pushoutAntidiagonalGen (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) (m : M) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
    letI := SB.isSquareZero
    pushoutProduct c SB :=
  -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
  letI := SB.commRing
  -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
  letI := SB.isSquareZero
  ⟨(inr (c m), -Solution.inclusion (RingHom.id A) (zeroKernelMap A B M) SB m), sorry⟩

/-- The antidiagonal generator is the pair (inr (c m), -inclusion m). -/
theorem pushoutAntidiagonalGen_apply (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) (m : M) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
    letI := SB.isSquareZero
    (pushoutAntidiagonalGen c SB m).1 =
      (inr (c m), -Solution.inclusion (RingHom.id A) (zeroKernelMap A B M) SB m) := sorry

/-- The antidiagonal ideal of M in N × B'. -/
def pushoutAntidiagonal (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
    letI := SB.isSquareZero
    Ideal (pushoutProduct c SB) :=
  -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
  letI := SB.commRing
  -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
  letI := SB.isSquareZero
  Ideal.span (Set.range (pushoutAntidiagonalGen c SB))

/-- The antidiagonal generators span `pushoutAntidiagonal`. -/
theorem pushoutAntidiagonal_eq_span (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
    letI := SB.isSquareZero
    pushoutAntidiagonal c SB = Ideal.span (Set.range (pushoutAntidiagonalGen c SB)) := sorry

/-- The class of `(inr n, 0)` in N × B'. -/
def pushoutInr (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) (n : N) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    pushoutProduct c SB :=
  -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
  letI := SB.commRing
  ⟨(inr n, 0), sorry⟩

/-- `pushoutInr n` is the pair `(inr n, 0)`. -/
theorem pushoutInr_apply (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) (n : N) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    (pushoutInr c SB n).1 = (inr n, 0) := sorry

/-- Pushout of 0 → M → B' → B → 0 along c : M →ₗ[B] N, as a square-zero
A-algebra extension of B by N. The middle ring is (N × B')/M. -/
def pushoutAlong (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) :
    @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _ :=
  -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
  letI := SB.commRing
  -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
  letI := SB.isSquareZero
  let fromA' :=
    (Ideal.Quotient.mk (pushoutAntidiagonal c SB)).comp
      (RingHom.codRestrict
        (RingHom.prod ((inlHom B N).comp (algebraMap A B)) SB.fromA')
        (pushoutProduct c SB) (fun _ ↦ sorry))
  let toB :=
    Ideal.Quotient.lift (pushoutAntidiagonal c SB)
      (SB.toB.comp (RingHom.pullbackSnd (trivFstRingHom B N) SB.toB)) sorry
  -- Local instance justification (proof-local temporary data): the pushout projection is a square-zero extension by construction.
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
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
    letI := SB.isSquareZero
    (pushoutAlong c SB).toB.comp (Ideal.Quotient.mk (pushoutAntidiagonal c SB)) =
      SB.toB.comp (RingHom.pullbackSnd (trivFstRingHom B N) SB.toB) := sorry

/-- The inverse kernel identification sends n to the class of (inr n, 0). -/
theorem pushoutAlong_kernelEquiv_symm (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) (n : N) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
    letI := SB.isSquareZero
    -- Local instance justification (proof-local temporary data): bundled pushout carrier ring is not globally registered.
    letI := (pushoutAlong c SB).commRing
    -- Local instance justification (proof-local temporary data): bundled pushout square-zero instance is not globally registered.
    letI := (pushoutAlong c SB).isSquareZero
    val ((pushoutAlong c SB).kernelEquiv.symm n) =
      Ideal.Quotient.mk (pushoutAntidiagonal c SB) (pushoutInr c SB n) := sorry

/-- The identity-base connecting diagram from B' to the pushout along c. -/
def pushoutAlongDiagram (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) :
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
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) :
    (pushoutAlongDiagram c SB).t' = RingHom.id A ∧
      (pushoutAlongDiagram c SB).t = RingHom.id A ∧
      (pushoutAlongDiagram c SB).g = RingHom.id B ∧
      (pushoutAlongDiagram c SB).ν = c.toAddMonoidHom := sorry

/-- The vertical map B' → B'_1 in the source pushout square. -/
def toPushoutAlong (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) :
    FittingMap (pushoutAlongDiagram c SB) :=
  -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
  letI := SB.commRing
  -- Local instance justification (proof-local temporary data): bundled `SB.isSquareZero` is not globally registered on the structure Solution.
  letI := SB.isSquareZero
  -- Local instance justification (proof-local temporary data): bundled pushout carrier ring is not globally registered.
  letI := (pushoutAlong c SB).commRing
  FittingMap.of (pushoutAlongDiagram c SB)
    ((Ideal.Quotient.mk (pushoutAntidiagonal c SB)).comp
      (RingHom.codRestrict
        (RingHom.prod ((inlHom B N).comp SB.toB) (RingHom.id SB.carrier))
        (pushoutProduct c SB) (fun _ ↦ sorry)))
    sorry sorry sorry

/-- `toPushoutAlong` is compatible with the projections to B and the maps from A. -/
theorem toPushoutAlong_spec (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _) :
    -- Local instance justification (proof-local temporary data): bundled `SB.commRing` is not globally registered on the structure Solution.
    letI := SB.commRing
    -- Local instance justification (proof-local temporary data): bundled pushout carrier ring is not globally registered.
    letI := (pushoutAlong c SB).commRing
    (pushoutAlong c SB).toB.comp (toPushoutAlong c SB).hom = SB.toB ∧
      (toPushoutAlong c SB).hom.comp SB.fromA' = (pushoutAlong c SB).fromA' := sorry

end SquareZeroExtension

end RingHom
