/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Prod
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.LocalRing.Pullback
public import ReasLib.RingTheory.RingHom.SquareZero.Diagram
public import ReasLib.RingTheory.RingHom.SquareZero.Split
public import ReasLib.RingTheory.RingHom.SquareZero.Presentation

/-!
# Pullback of a square-zero A-algebra extension along a base map

Given 0 → N → C' → C → 0 and A → B → C, the base pullback constructs
B'_2 = C' ×_C B as a square-zero A-algebra extension of B by N.
-/

@[expose] public section

noncomputable section

universe u

namespace RingHom.SquareZeroExtension

variable {A C N : Type u}
variable [CommRing A] [CommRing C] [Algebra A C]
variable [AddCommGroup N] [Module C N] [Module A N] [IsScalarTower A C N]

/-- Pullback of 0 → N → C' → C → 0 along B → C, as a square-zero A-algebra
extension of B by N. The middle ring is the fibre product C' ×_C B. -/
def pullbackAlong (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    Solution (B := B) (N := N) (RingHom.id A) (zeroKernelMap A B N) :=
  -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SC.commRing`.
  letI := SC.commRing
  -- Local instance justification (defeq pin): kernel modules must use the supplied `SC.isSquareZero`.
  letI := SC.isSquareZero
  let fromA' :=
    RingHom.codRestrict (RingHom.prod SC.fromA' (algebraMap A B))
      (SC.toB.pullback (algebraMap B C)) (fun _ ↦ sorry)
  let toB := RingHom.pullbackSnd SC.toB (algebraMap B C)
  -- Local instance justification (defeq pin): the explicitly specified fibre-product projection carries the square-zero laws required by Solution.of.
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
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SC.commRing`.
    letI := SC.commRing
    -- Local instance justification (defeq pin): fibre-product maps use the carrier ring supplied by the pullback solution.
    letI := (pullbackAlong B SC).commRing
    (pullbackAlong B SC).toB = RingHom.pullbackSnd SC.toB (algebraMap B C) := sorry

/-- The identity-base connecting diagram from the pullback along B → C to C'. -/
def pullbackAlongDiagram (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
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
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    (pullbackAlongDiagram B SC).t' = RingHom.id A ∧
      (pullbackAlongDiagram B SC).t = RingHom.id A ∧
      (pullbackAlongDiagram B SC).g = algebraMap B C ∧
      (pullbackAlongDiagram B SC).ν = AddMonoidHom.id N := sorry

/-- The canonical map from a base pullback to the original extension. -/
def fromPullbackAlong (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    FittingMap (pullbackAlongDiagram B SC) :=
  -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SC.commRing`.
  letI := SC.commRing
  -- Local instance justification (defeq pin): fibre-product maps use the carrier ring supplied by the pullback solution.
  letI := (pullbackAlong B SC).commRing
  FittingMap.of (pullbackAlongDiagram B SC)
    (RingHom.pullbackFst SC.toB (algebraMap B C)) sorry sorry sorry

/-- The C' projection of B'_2 is the first projection of the ring fibre product. -/
theorem pullbackAlong_fst (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SC.commRing`.
    letI := SC.commRing
    -- Local instance justification (defeq pin): fibre-product maps use the carrier ring supplied by the pullback solution.
    letI := (pullbackAlong B SC).commRing
    (fromPullbackAlong B SC).hom = RingHom.pullbackFst SC.toB (algebraMap B C) := sorry

/-- `fromPullbackAlong` is compatible with B → C and induces the identity on N. -/
theorem fromPullbackAlong_spec (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SC.commRing`.
    letI := SC.commRing
    -- Local instance justification (defeq pin): fibre-product maps use the carrier ring supplied by the pullback solution.
    letI := (pullbackAlong B SC).commRing
    SC.toB.comp (fromPullbackAlong B SC).hom =
        (algebraMap B C).comp (pullbackAlong B SC).toB ∧
      (fromPullbackAlong B SC).hom.comp (pullbackAlong B SC).fromA' = SC.fromA' := sorry

/-- The polynomial lift α' = (β' ∘ φ, α) of a presentation of B through C' ×_C B. -/
def pullbackAlong_presentationLift (B : Type u) [CommRing B] [Algebra A B] [Algebra B C]
    [IsScalarTower A B C] [Module B N] [IsScalarTower B C N] [IsScalarTower A B N]
    {ι κ : Type u} (G : Algebra.Generators A B ι) (H : Algebra.Generators A C κ)
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    -- Local instance justification (defeq pin): fibre-product maps use the carrier ring supplied by the pullback solution.
    letI := (pullbackAlong B SC).commRing
    -- Local instance justification (defeq pin): the polynomial lift uses the algebra structure induced by the pullback solution’s supplied structure map.
    letI : Algebra A (pullbackAlong B SC).carrier := (pullbackAlong B SC).fromA'.toAlgebra
    G.Ring →ₐ[A] (pullbackAlong B SC).carrier :=
  -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SC.commRing`.
  letI := SC.commRing
  -- Local instance justification (defeq pin): kernel modules must use the supplied `SC.isSquareZero`.
  letI := SC.isSquareZero
  -- Local instance justification (defeq pin): evaluation uses the algebra structure induced by the supplied SC.fromA'.
  letI : Algebra A SC.carrier := SC.fromA'.toAlgebra
  -- Local instance justification (defeq pin): fibre-product maps use the carrier ring supplied by the pullback solution.
  letI := (pullbackAlong B SC).commRing
  -- Local instance justification (defeq pin): the polynomial lift uses the algebra structure induced by the pullback solution’s supplied structure map.
  letI : Algebra A (pullbackAlong B SC).carrier := (pullbackAlong B SC).fromA'.toAlgebra
  let β' := presentationLift H SC
  let φ := Algebra.Generators.Hom.toAlgHom (Algebra.Generators.defaultHom G H)
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
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)) :
    -- Local instance justification (defeq pin): the dependent carrier ring must use the supplied `SC.commRing`.
    letI := SC.commRing
    -- Local instance justification (defeq pin): kernel modules must use the supplied `SC.isSquareZero`.
    letI := SC.isSquareZero
    -- Local instance justification (defeq pin): evaluation uses the algebra structure induced by the supplied SC.fromA'.
    letI : Algebra A SC.carrier := SC.fromA'.toAlgebra
    -- Local instance justification (defeq pin): fibre-product maps use the carrier ring supplied by the pullback solution.
    letI := (pullbackAlong B SC).commRing
    -- Local instance justification (defeq pin): the kernel identification uses the pullback solution’s square-zero structure.
    letI := (pullbackAlong B SC).isSquareZero
    -- Local instance justification (defeq pin): the polynomial lift uses the algebra structure induced by the pullback solution’s supplied structure map.
    letI : Algebra A (pullbackAlong B SC).carrier := (pullbackAlong B SC).fromA'.toAlgebra
    (pullbackAlong B SC).toB.comp (pullbackAlong_presentationLift B G H SC).toRingHom =
      algebraMap G.Ring B := sorry

end SquareZeroExtension

end RingHom
