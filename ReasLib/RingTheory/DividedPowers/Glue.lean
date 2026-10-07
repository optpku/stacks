module

public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Gluing Divided Power Structures

This module owns compatibility and gluing data for divided power structures on two ideals of a
commutative ring. It is independent of a chosen category of divided power rings.
-/

universe u

namespace DividedPowers

section

variable {A : Type u} [CommRing A] {I J : Ideal A}

/-- Two divided power structures agree on the intersection of their ideals. -/
@[stacks 07GQ "agreement on the intersection"]
abbrev agreeOnInf (γ : DividedPowers I) (δ : DividedPowers J) : Prop :=
  ∀ n : ℕ, ∀ ⦃x : A⦄, x ∈ I ⊓ J → γ.dpow n x = δ.dpow n x

/-- A divided power structure on the supremum ideal restricts to the given structures along
the identity ring map. -/
@[stacks 07GQ "compatibility on the supremum"]
abbrev compatibleOnSup (γ : DividedPowers I) (δ : DividedPowers J)
    (ε : DividedPowers (I ⊔ J)) : Prop :=
  IsDPMorphism γ ε (RingHom.id A) ∧ IsDPMorphism δ ε (RingHom.id A)

/-- Compatibility on the supremum includes the restriction from the first ideal. -/
theorem compatibleOnSup_left (γ : DividedPowers I) (δ : DividedPowers J)
    {ε : DividedPowers (I ⊔ J)} (hε : compatibleOnSup γ δ ε) :
    IsDPMorphism γ ε (RingHom.id A) := sorry

/-- Compatibility on the supremum includes the restriction from the second ideal. -/
theorem compatibleOnSup_right (γ : DividedPowers I) (δ : DividedPowers J)
    {ε : DividedPowers (I ⊔ J)} (hε : compatibleOnSup γ δ ε) :
    IsDPMorphism δ ε (RingHom.id A) := sorry

/-- Lemma 23.2.5 (1) (Tag 07GQ): divided power structures on two ideals agree on their product.
-/
@[stacks 07GQ "(1)"]
theorem coincide_on_mul (γ : DividedPowers I) (δ : DividedPowers J) {n : ℕ} {x : A}
    (hx : x ∈ I * J) :
    γ.dpow n x = δ.dpow n x := sorry

/-- A common compatible divided power structure on the supremum makes the two restrictions
agree on the intersection. -/
theorem agreeOnInf_of_compatibleOnSup (γ : DividedPowers I) (δ : DividedPowers J)
    {ε : DividedPowers (I ⊔ J)} (hε : compatibleOnSup γ δ ε) :
    agreeOnInf γ δ := sorry

namespace Glue

/-- The convolution candidate for gluing divided powers on `I` and `J`. Outside `I ⊔ J` it is
extended by zero, as required by Mathlib's total `DividedPowers.dpow` convention. The internal
choice of a decomposition is hidden behind `dpow_eq_of_add`. -/
noncomputable def dpow (γ : DividedPowers I) (δ : DividedPowers J) : ℕ → A → A :=
  open scoped Classical in fun n x ↦ if hx : x ∈ I ⊔ J then
    -- These local witnesses are the concrete decomposition data required by the total operation;
    -- decomposition independence is exposed by `dpow_eq_of_add` and the uniqueness API below.
    let h := Submodule.mem_sup.mp hx
    let y := Classical.choose h
    let h' := (Classical.choose_spec h).2
    let z := Classical.choose h'
    (Finset.antidiagonal n).sum fun k ↦ γ.dpow k.1 y * δ.dpow k.2 z
  else 0

/-- The convolution formula is independent of the selected decomposition: on `x + y` with
`x ∈ I` and `y ∈ J`, it is the expected sum of products of divided powers. -/
theorem dpow_eq_of_add (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    dpow γ δ n (x + y) =
      (Finset.antidiagonal n).sum fun k ↦ γ.dpow k.1 x * δ.dpow k.2 y := sorry

/-- The gluing candidate vanishes outside the supremum ideal. -/
theorem dpow_null (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {n : ℕ} {x : A} (hx : x ∉ I ⊔ J) :
    dpow γ δ n x = 0 := sorry

/-- The zeroth gluing operation is one on the supremum ideal. -/
theorem dpow_zero (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {x : A} (hx : x ∈ I ⊔ J) :
    dpow γ δ 0 x = 1 := sorry

/-- The first gluing operation is the identity on the supremum ideal. -/
theorem dpow_one (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {x : A} (hx : x ∈ I ⊔ J) :
    dpow γ δ 1 x = x := sorry

/-- Positive gluing operations preserve the supremum ideal. -/
theorem dpow_mem (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {n : ℕ} {x : A} (hn : n ≠ 0) (hx : x ∈ I ⊔ J) :
    dpow γ δ n x ∈ I ⊔ J := sorry

/-- The gluing candidate satisfies the divided-power addition identity. -/
theorem dpow_add (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {n : ℕ} {x y : A} (hx : x ∈ I ⊔ J)
    (hy : y ∈ I ⊔ J) :
    dpow γ δ n (x + y) =
      (Finset.antidiagonal n).sum fun k ↦ dpow γ δ k.1 x * dpow γ δ k.2 y := sorry

/-- The gluing candidate satisfies the divided-power scalar identity. -/
theorem dpow_mul (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {n : ℕ} {a x : A} (hx : x ∈ I ⊔ J) :
    dpow γ δ n (a * x) = a ^ n * dpow γ δ n x := sorry

/-- The gluing candidate satisfies the multiplication identity for divided powers. -/
theorem mul_dpow (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {m n : ℕ} {x : A} (hx : x ∈ I ⊔ J) :
    dpow γ δ m x * dpow γ δ n x =
      Nat.choose (m + n) m * dpow γ δ (m + n) x := sorry

/-- The gluing candidate satisfies the iterated divided-power identity. -/
theorem dpow_comp (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {m n : ℕ} {x : A} (hn : n ≠ 0)
    (hx : x ∈ I ⊔ J) :
    dpow γ δ m (dpow γ δ n x) =
      Nat.uniformBell m n * dpow γ δ (m * n) x := sorry

end Glue

/-- The canonical divided-power structure on `I ⊔ J` obtained by convolving two structures that
agree on `I ⊓ J`. Its operation is explicit; only decomposition independence and the
divided-power laws are proof obligations. -/
@[stacks 07GQ "canonical gluing on the supremum ideal"]
noncomputable def glue (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) : DividedPowers (I ⊔ J) where
  dpow := Glue.dpow γ δ
  dpow_null := Glue.dpow_null γ δ hagree
  dpow_zero := Glue.dpow_zero γ δ hagree
  dpow_one := Glue.dpow_one γ δ hagree
  dpow_mem := Glue.dpow_mem γ δ hagree
  dpow_add := Glue.dpow_add γ δ hagree
  dpow_mul := Glue.dpow_mul γ δ hagree
  mul_dpow := Glue.mul_dpow γ δ hagree
  dpow_comp := Glue.dpow_comp γ δ hagree

/-- The glued operation has the expected convolution formula on a sum of elements from the two
source ideals. -/
@[simp]
theorem glue_dpow_add (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {n : ℕ} {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    (glue γ δ hagree).dpow n (x + y) =
      (Finset.antidiagonal n).sum fun k ↦ γ.dpow k.1 x * δ.dpow k.2 y := sorry

/-- On the first ideal, the glued divided powers restrict to the first divided power structure. -/
@[simp]
theorem glue_dpow_of_mem_left (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {n : ℕ} {x : A} (hx : x ∈ I) :
    (glue γ δ hagree).dpow n x = γ.dpow n x := sorry

/-- On the second ideal, the glued divided powers restrict to the second divided power structure. -/
@[simp]
theorem glue_dpow_of_mem_right (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {n : ℕ} {x : A} (hx : x ∈ J) :
    (glue γ δ hagree).dpow n x = δ.dpow n x := sorry

/-- The glued divided powers restrict to both given structures. -/
theorem glue_compatibleOnSup (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) :
    compatibleOnSup γ δ (glue γ δ hagree) := sorry

/-- Any compatible divided-power structure on `I ⊔ J` is the explicit glued structure. -/
theorem eq_glue (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) {ε : DividedPowers (I ⊔ J)}
    (hε : compatibleOnSup γ δ ε) : ε = glue γ δ hagree := sorry

/-- Lemma 23.2.5 (2) (Tag 07GQ): divided power structures which agree on their intersection
glue uniquely to their supremum ideal. -/
@[stacks 07GQ]
theorem existsUnique_sup_of_agreeOnInf (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) :
    ∃! ε : DividedPowers (I ⊔ J), compatibleOnSup γ δ ε := sorry

/-- Compatible divided power structures on the supremum are uniquely determined by their two
restrictions. -/
theorem eq_of_compatibleOnSup (γ : DividedPowers I) (δ : DividedPowers J)
    {ε ε' : DividedPowers (I ⊔ J)}
    (hε : compatibleOnSup γ δ ε) (hε' : compatibleOnSup γ δ ε') :
    ε = ε' := sorry

/-- Divided power structures which agree on their intersection admit a compatible structure on
their supremum ideal. -/
theorem exists_sup_of_agreeOnInf (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) :
    ∃ ε : DividedPowers (I ⊔ J), compatibleOnSup γ δ ε := sorry

/-- The unique gluing condition for divided powers on a supremum ideal is equivalent to agreement
on the intersection. -/
theorem existsUnique_sup_iff_agreeOnInf (γ : DividedPowers I) (δ : DividedPowers J) :
    (∃! ε : DividedPowers (I ⊔ J), compatibleOnSup γ δ ε) ↔ agreeOnInf γ δ := sorry

end

end DividedPowers
