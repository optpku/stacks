/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Lemma_88_14_3_RigClosed

/-!
# Relative criteria for contracting a rig-closed prime
-/

@[expose] public section

universe u v

open Ideal.IsRigClosed

/-- Lemma 88.14.4: let `φ : A →+* B` be an adic, topologically finite type
homomorphism of Noetherian adic rings, let `q ⊂ B` be rig-closed, and write
`p = q.comap φ` and `a = topologicalNilradical A`. The following are
equivalent: the residue field of `B ⧸ q` is finite over `A ⧸ a`; `p` is
rig-closed in `A`; and the canonical map `A ⧸ p →+* B ⧸ q` is a finite ring
extension. -/
@[stacks 0GGB]
theorem Ideal.IsRigClosed.comap_tfae {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    List.TFAE
      [(residueFieldHom φ (h_adic.continuous) q).Finite,
        (q.comap φ).IsRigClosed,
        (Ideal.quotientMap q φ (le_rfl : q.comap φ ≤ q.comap φ)).Finite] :=
  sorry

/-- Along an adic, topologically finite type homomorphism of Noetherian adic
rings, the residue field of `B ⧸ q` is finite over `A ⧸ topologicalNilradical A`
if and only if `q.comap φ` is rig-closed. -/
theorem Ideal.IsRigClosed.residueFieldHom_finite_iff_comap
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    (residueFieldHom φ (h_adic.continuous) q).Finite ↔
      (q.comap φ).IsRigClosed :=
  sorry

/-- Along an adic, topologically finite type homomorphism of Noetherian adic
rings, `q.comap φ` is rig-closed if and only if the canonical map
`A ⧸ q.comap φ →+* B ⧸ q` is a finite ring extension. -/
theorem Ideal.IsRigClosed.comap_iff_quotientMap_finite
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    (q.comap φ).IsRigClosed ↔
      (Ideal.quotientMap q φ (le_rfl : q.comap φ ≤ q.comap φ)).Finite :=
  sorry

/-- Along an adic, topologically finite type homomorphism of Noetherian adic
rings, the residue field of `B ⧸ q` is finite over `A ⧸ topologicalNilradical A`
if and only if the canonical map `A ⧸ q.comap φ →+* B ⧸ q` is a finite ring
extension. -/
theorem Ideal.IsRigClosed.residueFieldHom_finite_iff_quotientMap_finite
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    (residueFieldHom φ (h_adic.continuous) q).Finite ↔
      (Ideal.quotientMap q φ (le_rfl : q.comap φ ≤ q.comap φ)).Finite :=
  sorry
