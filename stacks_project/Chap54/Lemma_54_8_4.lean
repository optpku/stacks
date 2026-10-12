/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.RationalSingularity.EssentialFiniteType
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 54.8.4: a two-dimensional normal local domain essentially of finite type and local
over a rational surface singularity, with the same fraction field, is a rational singularity. -/
@[stacks 0BG0]
#check (IsRationalSingularity.ofEssFiniteTypeOverring :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    (B : Type v) [CommRing B] [IsDomain B] [Algebra A B] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra B (FractionRing A)] [IsScalarTower A B (FractionRing A)]
    [IsFractionRing B (FractionRing A)] [IsNormalRing B],
    ringKrullDim B = 2 → IsRationalSingularity B)
