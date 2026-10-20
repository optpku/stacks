/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth.Algebraization
import StacksCheckRecall

@[expose] public section

universe u

/- Remark 88.7.3: Let `I` be an ideal of a Noetherian ring `A`. Let `B` be an
object of (88.2.0.2) which is rig-smooth over `(A, I)`. Then `B` is
`A`-algebra isomorphic to the `I`-adic completion of a finite type `A`-algebra
(Gabber–Zavyalov Theorem 1.2). This supercedes `Algebra.RigSmooth.exists_finiteTypeAlgEquiv`
(Proposition 88.6.3), `Algebra.RigEtale.exists_finiteTypeAlgEquiv`
(Lemma 88.10.2), and Elkik III Theorem 7 when `I` is principal. -/
@[stacks 0GAX]
#check (Algebra.RigSmooth.exists_finiteTypeAlgEquiv_of_isNoetherianRing :
  ∀ {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [Algebra.RigSmooth I B],
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B))
