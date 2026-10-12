/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Completion
public import ReasLib.AlgebraicGeometry.BivariantClass.Vanishing
import Lean.Elab.Tactic.Omega

/-!
# Products with addition of cutoff parameters

This is the explicit local correction of Stacks Remark 42.34.7. Low output
degrees use the genuine proper pushforward of each relative input. High output
degrees use the three original mixed pairings; both inputs cannot be ambient
there. The output cutoff is `p + q`, not `max p q`. The fixed-cutoff-one
convolution remains a separate construction in `Cutoff.Completion`.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Cutoff

variable {S : Scheme.{u}} [UniversallyCatenary S]
  (δ : S → ℤ) [IsDimensionFunction δ]
  {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
  (f : Z ⟶ X) [IsClosedImmersion f.left]

/-- Interpret a cutoff coefficient on the ambient scheme, using genuine proper
pushforward on the relative branch. -/
def ambientImage (p : ℕ) (n : ℤ) :
    Cutoff δ f p n →+ ChowCohomology.degree δ X.hom n :=
  -- Local instance justification (instance diamond): the intermediate relative group needs pointwiseAddCommGroup here; a global instance would overlap the identity-morphism Chow group instance.
  letI := pointwiseAddCommGroup δ f n
  if h : n < (p : ℤ) then toAmbient δ f h
  else (relativePushforward δ f n).comp (toRelative δ f h)

/-- Below the input cutoff the ambient image is the existing ambient projection. -/
theorem ambientImage_of_lt (p : ℕ) (n : ℤ) (h : n < (p : ℤ))
    (a : Cutoff δ f p n) :
    ambientImage δ f p n a = toAmbient δ f h a := by
  simp only [ambientImage, dif_pos h]

/-- At or above the input cutoff the ambient image is actual relative pushforward. -/
theorem ambientImage_of_ge (p : ℕ) (n : ℤ) (h : ¬n < (p : ℤ))
    (a : Cutoff δ f p n) :
    ambientImage δ f p n a = relativePushforward δ f n (toRelative δ f h a) := by
  simp only [ambientImage, dif_neg h, AddMonoidHom.comp_apply]

/-- Homogeneous product with output cutoff `p + q`. The impossible high-degree
ambient-ambient branch is eliminated by integer arithmetic. -/
def degreeMul (p q : ℕ) {i j : ℤ}
    (a : Cutoff δ f p i) (b : Cutoff δ f q j) : Cutoff δ f (p + q) (i + j) :=
  if hn : i + j < ((p + q : ℕ) : ℤ) then
    ofAmbient δ f hn
      (ChowCohomology.mul δ X.hom (ambientImage δ f p i a) (ambientImage δ f q j b))
  else if hi : i < (p : ℤ) then
    if hj : j < (q : ℤ) then
      False.elim (by omega)
    else
      ofRelative δ f hn
        (ambientMulRelative δ f i j (toAmbient δ f hi a) (toRelative δ f hj b))
  else if hj : j < (q : ℤ) then
    ofRelative δ f hn
      (relativeMulAmbient δ f i j (toRelative δ f hi a) (toAmbient δ f hj b))
  else
    ofRelative δ f hn
      (relativeMul δ f i j (toRelative δ f hi a) (toRelative δ f hj b))

/-- The low-degree output is the product of the actual ambient images. -/
theorem degreeMul_of_lt (p q : ℕ) {i j : ℤ}
    (a : Cutoff δ f p i) (b : Cutoff δ f q j)
    (hn : i + j < ((p + q : ℕ) : ℤ)) :
    degreeMul δ f p q a b = ofAmbient δ f hn
      (ChowCohomology.mul δ X.hom (ambientImage δ f p i a) (ambientImage δ f q j b)) := by
  simp only [degreeMul, dif_pos hn]

/-- The high-degree ambient-relative branch is the original specified pairing. -/
theorem degreeMul_of_ambient_relative (p q : ℕ) {i j : ℤ}
    (a : Cutoff δ f p i) (b : Cutoff δ f q j)
    (hn : ¬i + j < ((p + q : ℕ) : ℤ)) (hi : i < (p : ℤ)) (hj : ¬j < (q : ℤ)) :
    degreeMul δ f p q a b = ofRelative δ f hn
      (ambientMulRelative δ f i j (toAmbient δ f hi a) (toRelative δ f hj b)) := by
  simp only [degreeMul, dif_neg hn, dif_pos hi, dif_neg hj]

/-- The high-degree relative-ambient branch is the original specified pairing. -/
theorem degreeMul_of_relative_ambient (p q : ℕ) {i j : ℤ}
    (a : Cutoff δ f p i) (b : Cutoff δ f q j)
    (hn : ¬i + j < ((p + q : ℕ) : ℤ)) (hi : ¬i < (p : ℤ)) (hj : j < (q : ℤ)) :
    degreeMul δ f p q a b = ofRelative δ f hn
      (relativeMulAmbient δ f i j (toRelative δ f hi a) (toAmbient δ f hj b)) := by
  simp only [degreeMul, dif_neg hn, dif_neg hi, dif_pos hj]

/-- The high-degree relative-relative branch is the original specified pairing. -/
theorem degreeMul_of_relative_relative (p q : ℕ) {i j : ℤ}
    (a : Cutoff δ f p i) (b : Cutoff δ f q j)
    (hn : ¬i + j < ((p + q : ℕ) : ℤ)) (hi : ¬i < (p : ℤ)) (hj : ¬j < (q : ℤ)) :
    degreeMul δ f p q a b = ofRelative δ f hn
      (relativeMul δ f i j (toRelative δ f hi a) (toRelative δ f hj b)) := by
  simp only [degreeMul, dif_neg hn, dif_neg hi, dif_neg hj]

/-- Proper base change for the closed immersion identifies the ambient action
of the first relative pushforward with the prescribed relative product. -/
theorem ambientMulRelative_pushforward {i j : ℤ}
    (a : BivariantClass δ f i) (b : BivariantClass δ f j) :
    ambientMulRelative δ f i j (relativePushforward δ f i a) b =
      relativeMul δ f i j a b := sorry

/-- Compatibility of cap with proper pushforward identifies the other ambient
action with that same specified relative product. -/
theorem relativeMulAmbient_pushforward {i j : ℤ}
    (a : BivariantClass δ f i) (b : BivariantClass δ f j) :
    relativeMulAmbient δ f i j a (relativePushforward δ f j b) =
      relativeMul δ f i j a b := sorry

/-- The ambient image of the specified product is the ordinary ambient product.
This is the proper-pushforward projection formula in each actual branch. -/
theorem ambientImage_degreeMul (p q : ℕ) {i j : ℤ}
    (a : Cutoff δ f p i) (b : Cutoff δ f q j) :
    ambientImage δ f (p + q) (i + j) (degreeMul δ f p q a b) =
      ChowCohomology.mul δ X.hom (ambientImage δ f p i a) (ambientImage δ f q j b) := sorry

/-- Coefficientwise associativity for the actual sum-cutoff operation. `HEq`
accounts only for associativity of the two index additions. -/
theorem degreeMul_assoc (p q r : ℕ) {i j k : ℤ}
    (a : Cutoff δ f p i) (b : Cutoff δ f q j) (c : Cutoff δ f r k) :
    HEq (degreeMul δ f (p + q) r (degreeMul δ f p q a b) c)
      (degreeMul δ f p (q + r) a (degreeMul δ f q r b c)) := sorry

/-- Genuine transport along equality of degree indices. -/
def castDegree {p : ℕ} {i j : ℤ} (h : i = j) (a : Cutoff δ f p i) : Cutoff δ f p j :=
  h ▸ a

/-- A coefficient of the sum-cutoff convolution, using a finite antidiagonal. -/
def familyMul (p q : ℕ) (a : Family δ f p) (b : Family δ f q) : Family δ f (p + q) :=
  fun n ↦ (Finset.antidiagonal n).attach.sum fun ij ↦
    castDegree δ f
      ((Nat.cast_add ij.1.1 ij.1.2).symm.trans
        (congrArg (fun k : ℕ ↦ (k : ℤ)) (Finset.mem_antidiagonal.mp ij.2)))
      (degreeMul δ f p q (a ij.1.1) (b ij.1.2))

/-- The completed nonnegative product is the explicit finite coefficient sum. -/
theorem familyMul_apply (p q : ℕ) (a : Family δ f p) (b : Family δ f q) (n : ℕ) :
    familyMul δ f p q a b n = (Finset.antidiagonal n).attach.sum fun ij ↦
      castDegree δ f
        ((Nat.cast_add ij.1.1 ij.1.2).symm.trans
          (congrArg (fun k : ℕ ↦ (k : ℤ)) (Finset.mem_antidiagonal.mp ij.2)))
        (degreeMul δ f p q (a ij.1.1) (b ij.1.2)) := rfl

/-- True fixed-map distributivity in the first input, from bilinearity of cap
composition and proper pushforward. -/
theorem familyMul_add_left (p q : ℕ) (a a' : Family δ f p) (b : Family δ f q) :
    familyMul δ f p q (a + a') b = familyMul δ f p q a b + familyMul δ f p q a' b := sorry

/-- True fixed-map distributivity in the second input. -/
theorem familyMul_add_right (p q : ℕ) (a : Family δ f p) (b b' : Family δ f q) :
    familyMul δ f p q a (b + b') = familyMul δ f p q a b + familyMul δ f p q a b' := sorry

/-- Transport only the natural cutoff parameter along an actual equality. -/
def castFamily {p q : ℕ} (h : p = q) (a : Family δ f p) : Family δ f q := h ▸ a

/-- Sum-cutoff associativity. Proper pushforward is compatible with ambient
actions and `j(m)·n = m⋆n = m·j(n)` for the prescribed relative multiplication.
The two output parameters are identified only by `Nat.add_assoc`. -/
theorem familyMul_assoc (p q r : ℕ)
    (a : Family δ f p) (b : Family δ f q) (c : Family δ f r) :
    castFamily δ f (Nat.add_assoc p q r)
        (familyMul δ f (p + q) r (familyMul δ f p q a b) c) =
      familyMul δ f p (q + r) a (familyMul δ f q r b c) := sorry

/-- Negative-degree bivariant classes of a closed immersion vanish. On each
integral test scheme their cap lands above the dimension of its closed inverse
image; the existing fundamental-class vanishing criterion then applies. -/
theorem relative_eq_zero_of_negative (n : ℤ) (hn : n < 0) (c : BivariantClass δ f n) :
    c = pointwiseZero δ f n := sorry

/-- Negative ambient degrees vanish by the same dimension argument for the identity. -/
theorem ambient_eq_zero_of_negative (n : ℤ) (hn : n < 0)
    (c : ChowCohomology.degree δ X.hom n) : c = 0 := sorry

/-- Every negative cutoff degree is zero; the cutoff is a nonnegative natural number. -/
theorem eq_zero_of_negative (p : ℕ) (n : ℤ) (hn : n < 0) (c : Cutoff δ f p n) :
    c = 0 := sorry

/-- The full integer-indexed completed cutoff carrier from the original source. -/
abbrev Completed (p : ℕ) : Type (u + 1) := ∀ n : ℤ, Cutoff δ f p n

/-- The full carrier retains every original integer degree and its cutoff branch. -/
theorem completed_def (p : ℕ) :
    Completed δ f p = ∀ n : ℤ,
      if n < (p : ℤ) then ChowCohomology.degree δ X.hom n else BivariantClass δ f n := rfl

/-- Restriction to nonnegative coefficients, with no choice of representatives. -/
def toNonnegative (p : ℕ) (a : Completed δ f p) : Family δ f p := fun n ↦ a (n : ℤ)

/-- Explicit extension by the canonical zero in negative degrees. -/
def ofNonnegative (p : ℕ) (a : Family δ f p) : Completed δ f p
  | .ofNat n => a n
  | .negSucc _ => 0

/-- The actual restriction/zero-extension equivalence. Negative vanishing
supplies only its inverse law, not any new data or existence-based choice. -/
def completedEquivFamily (p : ℕ) : Completed δ f p ≃+ Family δ f p where
  toFun := toNonnegative δ f p
  invFun := ofNonnegative δ f p
  left_inv a := by
    funext n
    cases n with
    | ofNat n => rfl
    | negSucc n =>
      exact (eq_zero_of_negative δ f p (Int.negSucc n) (by omega) (a _)).symm
  right_inv a := rfl
  map_add' a b := rfl

/-- The forward map of the comparison is actual coefficient restriction. -/
theorem completedEquivFamily_apply (p : ℕ) (a : Completed δ f p) (n : ℕ) :
    completedEquivFamily δ f p a n = a (n : ℤ) := rfl

/-- The inverse map is the specified zero extension on negative coefficients. -/
theorem completedEquivFamily_symm_apply_negSucc (p : ℕ) (a : Family δ f p) (n : ℕ) :
    (completedEquivFamily δ f p).symm a (Int.negSucc n) = 0 := rfl

/-- Product on the original integer-indexed carriers, computed by finite
nonnegative convolution and explicit zero-extension. -/
def completedMul (p q : ℕ) (a : Completed δ f p) (b : Completed δ f q) :
    Completed δ f (p + q) :=
  ofNonnegative δ f (p + q)
    (familyMul δ f p q (toNonnegative δ f p a) (toNonnegative δ f q b))

/-- Nonnegative coefficients of the full product are the actual finite convolution. -/
theorem completedMul_apply_nat (p q n : ℕ) (a : Completed δ f p) (b : Completed δ f q) :
    completedMul δ f p q a b (n : ℤ) =
      familyMul δ f p q (toNonnegative δ f p a) (toNonnegative δ f q b) n := rfl

/-- Negative coefficients of the full product are the canonical zero. -/
theorem completedMul_apply_negSucc (p q n : ℕ)
    (a : Completed δ f p) (b : Completed δ f q) :
    completedMul δ f p q a b (Int.negSucc n) = 0 := rfl

/-- True transport in the cutoff parameter of the full integer-indexed carrier. -/
def castCompleted {p q : ℕ} (h : p = q) (a : Completed δ f p) : Completed δ f q := h ▸ a

/-- Full-carrier associativity for addition of cutoffs, with no algebra assumption
on any arbitrary fixed cutoff. -/
theorem completedMul_assoc (p q r : ℕ)
    (a : Completed δ f p) (b : Completed δ f q) (c : Completed δ f r) :
    castCompleted δ f (Nat.add_assoc p q r)
        (completedMul δ f (p + q) r (completedMul δ f p q a b) c) =
      completedMul δ f p (q + r) a (completedMul δ f q r b c) := sorry

/-- The full-carrier product is additive in its first input. -/
theorem completedMul_add_left (p q : ℕ)
    (a a' : Completed δ f p) (b : Completed δ f q) :
    completedMul δ f p q (a + a') b =
      completedMul δ f p q a b + completedMul δ f p q a' b := sorry

/-- The full-carrier product is additive in its second input. -/
theorem completedMul_add_right (p q : ℕ)
    (a : Completed δ f p) (b b' : Completed δ f q) :
    completedMul δ f p q a (b + b') =
      completedMul δ f p q a b + completedMul δ f p q a b' := sorry

end AlgebraicGeometry.BivariantClass.Cutoff
