module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.LocalRing.Pullback
public import stacks_project.Chap91.Lemma_91_2_1_Diagram
public import stacks_project.Chap91.Lemma_91_2_3
public import stacks_project.Chap91.Remark_91_2_4_Lift

/-!
# Pullback of a square-zero A-algebra extension along a base map

Given 0 → N → C' → C → 0 and A → B → C, the source constructs
B'_2 = C' ×_C B as a square-zero A-algebra extension of B by N.
-/

@[expose] public section

noncomputable section

universe u

open Algebra Algebra.Generators Algebra.Extension
open MvPolynomial

namespace RingHom.SquareZeroExtension

variable {A C N : Type u}
variable [CommRing A] [CommRing C] [Algebra A C]
variable [AddCommGroup N] [Module C N] [Module A N] [IsScalarTower A C N]

/-- Pullback of 0 → N → C' → C → 0 along B → C, as a square-zero A-algebra
extension of B by N. The middle ring is the fibre product C' ×_C B. -/
def pullbackAlong (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    @Solution A A _ _ B _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A B N) _ :=
  -- Local instance justification (proof-local temporary data): bundled `SC.commRing` is not globally registered on the structure Solution.
  letI := SC.commRing
  -- Local instance justification (proof-local temporary data): bundled `SC.isSquareZero` is not globally registered on the structure Solution.
  letI := SC.isSquareZero
  let fromA' :=
    RingHom.codRestrict (RingHom.prod SC.fromA' (algebraMap A B))
      (SC.toB.pullback (algebraMap B C)) (fun _ ↦ sorry)
  let toB := RingHom.pullbackSnd SC.toB (algebraMap B C)
  -- Local instance justification (proof-local temporary data): the pullback projection is a square-zero extension by construction.
  letI : toB.IsSquareZeroExtension := ⟨sorry, sorry⟩
  Solution.of (RingHom.id A) (zeroKernelMap A B N) fromA' toB sorry
    { toFun := fun x ↦
        SC.kernelEquiv
          (ofMem (x := RingHom.pullbackFst SC.toB (algebraMap B C) x.1) sorry)
      invFun := fun n ↦
        ofMem
          (x :=
            ⟨(Solution.inclusion (RingHom.id A) (zeroKernelMap A C N) SC n, (0 : B)), sorry⟩)
          sorry
      left_inv := sorry
      right_inv := sorry
      map_add' := sorry
      map_smul' := sorry }
    sorry

/-- The projection B'_2 → B is the second projection of the ring fibre product. -/
theorem pullbackAlong_toB (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    -- Local instance justification (proof-local temporary data): bundled `SC.commRing` is not globally registered on the structure Solution.
    letI := SC.commRing
    -- Local instance justification (proof-local temporary data): bundled pullback carrier ring is not globally registered.
    letI := (pullbackAlong B SC).commRing
    (pullbackAlong B SC).toB = RingHom.pullbackSnd SC.toB (algebraMap B C) := sorry

/-- The identity-base connecting diagram from the pullback along B → C to C'. -/
def pullbackAlongDiagram (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    RelativeDiagram (pullbackAlong B SC) SC where
  t' := RingHom.id A
  t := RingHom.id A
  g := algebraMap B C
  ν := AddMonoidHom.id N
  map_smul_ν := sorry
  comm_base := sorry
  comm_alg := sorry
  comm_kernel := sorry

/-- `pullbackAlongDiagram` has identity maps on A, g = algebraMap B C, and ν = id. -/
theorem pullbackAlongDiagram_spec (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    (pullbackAlongDiagram B SC).t' = RingHom.id A ∧
      (pullbackAlongDiagram B SC).t = RingHom.id A ∧
      (pullbackAlongDiagram B SC).g = algebraMap B C ∧
      (pullbackAlongDiagram B SC).ν = AddMonoidHom.id N := sorry

/-- The vertical map B'_2 → C' in the source pullback square. -/
def fromPullbackAlong (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    FittingMap (pullbackAlongDiagram B SC) :=
  -- Local instance justification (proof-local temporary data): bundled `SC.commRing` is not globally registered on the structure Solution.
  letI := SC.commRing
  -- Local instance justification (proof-local temporary data): bundled pullback carrier ring is not globally registered.
  letI := (pullbackAlong B SC).commRing
  FittingMap.of (pullbackAlongDiagram B SC)
    (RingHom.pullbackFst SC.toB (algebraMap B C)) sorry sorry sorry

/-- The C' projection of B'_2 is the first projection of the ring fibre product. -/
theorem pullbackAlong_fst (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    -- Local instance justification (proof-local temporary data): bundled `SC.commRing` is not globally registered on the structure Solution.
    letI := SC.commRing
    -- Local instance justification (proof-local temporary data): bundled pullback carrier ring is not globally registered.
    letI := (pullbackAlong B SC).commRing
    (fromPullbackAlong B SC).hom = RingHom.pullbackFst SC.toB (algebraMap B C) := sorry

/-- `fromPullbackAlong` is compatible with B → C and induces the identity on N. -/
theorem fromPullbackAlong_spec (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    -- Local instance justification (proof-local temporary data): bundled `SC.commRing` is not globally registered on the structure Solution.
    letI := SC.commRing
    -- Local instance justification (proof-local temporary data): bundled pullback carrier ring is not globally registered.
    letI := (pullbackAlong B SC).commRing
    SC.toB.comp (fromPullbackAlong B SC).hom =
        (algebraMap B C).comp (pullbackAlong B SC).toB ∧
      (fromPullbackAlong B SC).hom.comp (pullbackAlong B SC).fromA' = SC.fromA' := sorry

/-- The source lift α' = (β' ∘ φ, α) of a presentation of B through B'_2 = C' ×_C B. -/
def pullbackAlong_presentationLift (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    {ι κ : Type u} (G : Algebra.Generators A B ι) (H : Algebra.Generators A C κ)
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    -- Local instance justification (proof-local temporary data): bundled pullback carrier ring is not globally registered.
    letI := (pullbackAlong B SC).commRing
    -- Local instance justification (proof-local temporary data): the A-algebra structure on B'_2 is the structure map of the solution, not an ambient Algebra A (pullbackAlong B SC).carrier.
    letI : Algebra A (pullbackAlong B SC).carrier := (pullbackAlong B SC).fromA'.toAlgebra
    G.Ring →ₐ[A] (pullbackAlong B SC).carrier :=
  -- Local instance justification (proof-local temporary data): bundled `SC.commRing` is not globally registered on the structure Solution.
  letI := SC.commRing
  -- Local instance justification (proof-local temporary data): bundled `SC.isSquareZero` is not globally registered on the structure Solution.
  letI := SC.isSquareZero
  -- Local instance justification (proof-local temporary data): the A-algebra structure on C' is the structure map of the solution, not an ambient Algebra A SC.carrier.
  letI : Algebra A SC.carrier := SC.fromA'.toAlgebra
  -- Local instance justification (proof-local temporary data): bundled pullback carrier ring is not globally registered.
  letI := (pullbackAlong B SC).commRing
  -- Local instance justification (proof-local temporary data): the A-algebra structure on B'_2 is the structure map of the solution, not an ambient Algebra A (pullbackAlong B SC).carrier.
  letI : Algebra A (pullbackAlong B SC).carrier := (pullbackAlong B SC).fromA'.toAlgebra
  let β' := presentationLift H SC
  let φ := Hom.toAlgHom (defaultHom G H)
  let α := MvPolynomial.aeval G.val
  { toFun := fun p ↦ ⟨(β' (φ p), α p), sorry⟩
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    map_add' := sorry
    commutes' := sorry }

/-- `pullbackAlong_presentationLift` recovers α after composing with B'_2 → B. -/
theorem pullbackAlong_presentationLift_comp (B : Type u) [CommRing B] [Algebra A B]
    [Algebra B C] [IsScalarTower A B C] [Module B N] [IsScalarTower B C N]
    [IsScalarTower A B N] {ι κ : Type u}
    (G : Algebra.Generators A B ι) (H : Algebra.Generators A C κ)
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    -- Local instance justification (proof-local temporary data): bundled `SC.commRing` is not globally registered on the structure Solution.
    letI := SC.commRing
    -- Local instance justification (proof-local temporary data): bundled `SC.isSquareZero` is not globally registered on the structure Solution.
    letI := SC.isSquareZero
    -- Local instance justification (proof-local temporary data): the A-algebra structure on C' is the structure map of the solution, not an ambient Algebra A SC.carrier.
    letI : Algebra A SC.carrier := SC.fromA'.toAlgebra
    -- Local instance justification (proof-local temporary data): bundled pullback carrier ring is not globally registered.
    letI := (pullbackAlong B SC).commRing
    -- Local instance justification (proof-local temporary data): bundled pullback square-zero instance is not globally registered.
    letI := (pullbackAlong B SC).isSquareZero
    -- Local instance justification (proof-local temporary data): the A-algebra structure on B'_2 is the structure map of the solution, not an ambient Algebra A (pullbackAlong B SC).carrier.
    letI : Algebra A (pullbackAlong B SC).carrier := (pullbackAlong B SC).fromA'.toAlgebra
    (pullbackAlong B SC).toB.comp (pullbackAlong_presentationLift B G H SC).toRingHom =
      algebraMap G.Ring B := sorry

end SquareZeroExtension

end RingHom
