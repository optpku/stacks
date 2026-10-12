/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant systems of commutative rings

This leaf identifies the directed direct limit of a constant commutative-ring
system with its value.  It is deliberately independent of any chosen base
algebra structure.
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit

variable (A : Type u) [CommRing A]
variable (I : Type v) [Preorder I] [Nonempty I]

/-- Identity transition maps make a constant commutative-ring system into a
canonical directed system. -/
@[stacks 031N "constant direct limit"]
instance constantDirectedSystem :
    DirectedSystem (fun _ : I ↦ A)
      (fun _ _ _ ↦ (RingHom.id A : A →+* A)) where
  map_self := sorry
  map_map := sorry

/-- The directed direct limit of the constant `A`-system with identity
transition maps is canonically isomorphic to `A`. -/
@[stacks 031N "constant direct limit"]
noncomputable def constantEquiv [IsDirectedOrder I] :
    Ring.DirectLimit (fun _ : I ↦ A)
      (fun _ _ _ ↦ (RingHom.id A : A →+* A)) ≃+* A :=
  RingEquiv.ofRingHom
    (Ring.DirectLimit.lift
      (fun _ : I ↦ A) (fun _ _ _ ↦ (RingHom.id A : A →+* A)) A
      (fun _ ↦ RingHom.id A) sorry)
    (Ring.DirectLimit.of
      (fun _ : I ↦ A) (fun _ _ _ ↦ (RingHom.id A : A →+* A))
      (Classical.choice (show Nonempty I from inferInstance)))
    sorry
    sorry

/-- The constant-system direct-limit equivalence evaluates every stage
representative to its underlying element. -/
@[simp, stacks 031N "constant direct limit"]
theorem constantEquiv_of [IsDirectedOrder I] (i : I) (a : A) :
    constantEquiv A I
        (Ring.DirectLimit.of
          (fun _ : I ↦ A) (fun _ _ _ ↦ (RingHom.id A : A →+* A)) i a) = a := sorry

/-- The inverse of the constant-system direct-limit equivalence sends an
element to its representative in any chosen stage. -/
@[simp, stacks 031N "constant direct limit"]
theorem constantEquiv_symm_of [IsDirectedOrder I] (i : I) (a : A) :
    (constantEquiv A I).symm a =
      Ring.DirectLimit.of
        (fun _ : I ↦ A) (fun _ _ _ ↦ (RingHom.id A : A →+* A)) i a := sorry

/-- The constant-system direct-limit equivalence composes with every stage
map as the identity of `A`. -/
@[simp, stacks 031N "constant direct limit"]
theorem constantEquiv_comp_of [IsDirectedOrder I] (i : I) :
    (constantEquiv A I).toRingHom.comp
        (Ring.DirectLimit.of
          (fun _ : I ↦ A) (fun _ _ _ ↦ (RingHom.id A : A →+* A)) i) =
      RingHom.id A := sorry

section Map

variable {A₁ : Type u} {A₂ : Type v} [CommRing A₁] [CommRing A₂]
variable (J : Type w) [Preorder J]

/-- Under the canonical equivalences from constant direct limits, the map
induced by `f` is exactly `f`. -/
@[stacks 031N "constant direct limit"]
theorem constantEquiv_map [Nonempty J] [IsDirectedOrder J] (f : A₁ →+* A₂)
    (hcomm : ∀ i j hij,
      f.comp (RingHom.id A₁) = (RingHom.id A₂).comp f) :
    (constantEquiv A₂ J).toRingHom.comp
        (Ring.DirectLimit.map (fun _ : J ↦ f) hcomm) =
      f.comp (constantEquiv A₁ J).toRingHom := sorry

end Map

end Ring.DirectLimit
