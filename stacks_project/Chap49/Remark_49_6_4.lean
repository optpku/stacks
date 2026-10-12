/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import stacks_project.Chap49.«49_6_4_1»

universe u v

/- Remark 49.6.4: for a quasi-finite map of Noetherian rings, contraction on a
chosen finite model extends canonically to the `B`-bilinear pairing from
`Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open` and the annihilator
of `KaehlerDifferential.ideal A B` to `B`. The formula and canonicity are exposed by
`Algebra.RelativeDualizingModule.noetherPairing_tmul` and
`Algebra.RelativeDualizingModule.noetherPairing_unique`. -/
@[stacks 0BVP] #check
  (Algebra.RelativeDualizingModule.noetherPairing :
    ∀ (A : Type u) (B' B : Type v)
      [CommRing A] [CommRing B'] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
      (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
      (h_open : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap B' B)))),
      Algebra.RelativeDualizingModule.of A B' B h_quasiFinite h_open →ₗ[B]
        ((KaehlerDifferential.ideal A B).annihilator →ₗ[B] B))

/- The finite-model contraction pairing used in the construction. -/
#check Algebra.RelativeDualizingModule.finiteNoetherPairing

/- The scalar-extended pure-tensor formula for the canonical pairing. -/
#check Algebra.RelativeDualizingModule.noetherPairing_tmul

/- Uniqueness of the pairing satisfying the pure-tensor formula. -/
#check Algebra.RelativeDualizingModule.noetherPairing_unique
