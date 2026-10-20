/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.FiniteType.Reduction.Noetherian
import StacksCheckRecall

/-!
# Finite type on reductions versus topological finite type for adic Noetherian maps
-/

@[expose] public section

universe u

open TopologicalRing

/- Lemma 88.12.6: For an adic homomorphism between Noetherian adic rings,
finite type on reduction is equivalent to topological finite type. -/
@[stacks 0GG6] #check (RingHom.isFiniteTypeOnReduction_iff_topologicallyOfFiniteType :
    ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom),
    φ.IsFiniteTypeOnReduction ↔ φ.TopologicallyOfFiniteType)

/- An adic, topologically finite type homomorphism of Noetherian adic rings is
of finite type on reduction. -/
#check (RingHom.IsFiniteTypeOnReduction.of_isAdicHom_topologicallyOfFiniteType :
    ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType),
    φ.IsFiniteTypeOnReduction)

/- For an adic algebra map of Noetherian adic rings, finite type on reduction
is equivalent to the algebra being topologically of finite type. -/
#check (Algebra.TopologicallyOfFiniteType.iff_isFiniteTypeOnReduction :
    ∀ {R A : Type u}
    [CommRing R] [TopologicalSpace R] [IsAdicRing R] [IsNoetherianRing R]
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [Algebra R A] (h_adic : (algebraMap R A).IsAdicHom),
    (algebraMap R A).IsFiniteTypeOnReduction ↔ Algebra.TopologicallyOfFiniteType R A)
