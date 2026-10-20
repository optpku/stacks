/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.SquareZero.Transport
import StacksCheckRecall

/-!
# Functoriality of square-zero A-algebra extensions by pushout and pullback

In the identity-base setting of Lemma 91.2.5, the pushout of 0 → M → B' → B → 0
along c : M → N is B'_1 = (N × B')/M, and the pullback of 0 → N → C' → C → 0
along B → C is B'_2 = C' ×_C B. An A-algebra map B' → C' compatible with B → C
and c exists iff B'_1 ≅ B'_2 as A-algebra extensions of B by N.
-/

@[expose] public section

universe u

open RingHom.SquareZeroExtension

variable {A B C M N : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup N] [Module C N] [Module B N] [Module A N]
variable [IsScalarTower B C N] [IsScalarTower A C N] [IsScalarTower A B N]

/- Remark 91.2.6 (1) Using pushout along c : M →ₗ[B] N we construct an extension
0 → N → B'_1 → B → 0 by setting B'_1 = (N × B')/M where M is antidiagonally
embedded. -/
@[stacks 0GPW] #check (RingHom.SquareZeroExtension.pushoutAlong :
  (c : M →ₗ[B] N) →
    Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M) →
    Solution (B := B) (N := N) (RingHom.id A) (zeroKernelMap A B N))

/- Remark 91.2.6 (2) Using pullback along B → C we construct an extension
0 → N → B'_2 → B → 0 by setting B'_2 = C' ×_C B, the fibre product of rings. -/
@[stacks 0GPW] #check (RingHom.SquareZeroExtension.pullbackAlong B :
  Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N) →
    Solution (B := B) (N := N) (RingHom.id A) (zeroKernelMap A B N))

/- Remark 91.2.6 (3) There exists an A-algebra map B' → C' compatible with
B → C and c if and only if pushoutAlong c SB is isomorphic to pullbackAlong B SC
as A-algebra extensions of B by N. -/
@[stacks 0GPW] #check (RingHom.SquareZeroExtension.exists_fittingMap_iff_isoClass :
  ∀ (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M))
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)),
    Nonempty (FittingMap (RelativeDiagram.ofAlgebraMap c SB SC)) ↔
      isoClassMk (pushoutAlong c SB) = isoClassMk (pullbackAlong B SC))

/- Remark 91.2.6 (4) Via the bijection of Lemma 91.2.3, pushoutAlong c SB is the
image of the class of SB under Ext¹_B(NL_{B/A}, M) → Ext¹_B(NL_{B/A}, N). -/
@[stacks 0GPW] #check (RingHom.SquareZeroExtension.pushoutAlong_extClass :
  ∀ (c : M →ₗ[B] N)
    (SB : Solution (B := B) (N := M) (RingHom.id A) (zeroKernelMap A B M)),
    (algebraExtensionEquiv A B N).symm (isoClassMk (pushoutAlong c SB)) =
      extOneNaiveCotangent_map c
        ((algebraExtensionEquiv A B M).symm (isoClassMk SB)))

/- Remark 91.2.6 (5) Via the bijection of Lemma 91.2.3, pullbackAlong B SC is the
image of the class of SC under Ext¹_C(NL_{C/A}, N) → Ext¹_B(NL_{B/A}, N). -/
@[stacks 0GPW] #check (RingHom.SquareZeroExtension.pullbackAlong_extClass :
  ∀
    (SC : Solution (B := C) (N := N) (RingHom.id A) (zeroKernelMap A C N)),
    (algebraExtensionEquiv A B N).symm (isoClassMk (pullbackAlong B SC)) =
      extOneNaiveCotangent_comap B
        ((algebraExtensionEquiv A C N).symm (isoClassMk SC)))
