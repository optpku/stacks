/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.BivariantClass.OpenRestriction.Completion

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry.ChowCohomology.Nonnegative

variable {S X : Scheme.{u}} (delta : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction delta] [LocallyOfFiniteType p]

/-- The degree-`n` part of nonnegative Chow cohomology. -/
abbrev degree (n : ℕ) : Type (u + 1) := ChowCohomology.degree delta p (n : ℤ)

/-- The nonnegative Chow cohomology direct sum. -/
abbrev ring : Type (u + 1) := ⨁ n : ℕ, degree delta p n

/-- Addition of natural degrees agrees with addition after coercion to integers. -/
theorem degree_add (i j : ℕ) : (i : ℤ) + (j : ℤ) = ((i + j : ℕ) : ℤ) := sorry

/-- Homogeneous multiplication on nonnegative Chow cohomology. -/
def mul {i j : ℕ} (c : degree delta p i) (d : degree delta p j) :
    degree delta p (i + j) :=
  BivariantClass.Nonnegative.castGrading delta (degree_add i j)
    (ChowCohomology.mul delta p c d)

/-- Homogeneous multiplication by zero on the right vanishes. -/
theorem mul_zero {i j : ℕ} (c : degree delta p i) :
    mul delta p c (0 : degree delta p j) = 0 := sorry

/-- Homogeneous multiplication by zero on the left vanishes. -/
theorem zero_mul {i j : ℕ} (d : degree delta p j) :
    mul delta p (0 : degree delta p i) d = 0 := sorry

/-- Homogeneous multiplication distributes over addition in the right variable. -/
theorem mul_add {i j : ℕ} (c : degree delta p i) (d e : degree delta p j) :
    mul delta p c (d + e) = mul delta p c d + mul delta p c e := sorry

/-- Homogeneous multiplication distributes over addition in the left variable. -/
theorem add_mul {i j : ℕ} (c d : degree delta p i) (e : degree delta p j) :
    mul delta p (c + d) e = mul delta p c e + mul delta p d e := sorry

/-- Nonnegative bivariant composition supplies the graded multiplication data. -/
instance instGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (degree delta p) where
  mul := fun c d ↦ mul delta p c d
  mul_zero := mul_zero delta p
  zero_mul := zero_mul delta p
  mul_add := mul_add delta p
  add_mul := add_mul delta p

/-- The degree-zero identity bivariant class supplies the graded unit. -/
instance instGOne : GradedMonoid.GOne (degree delta p) where
  one := ChowCohomology.one delta p

/-- The degree-zero identity is a left identity on the nonnegative graded monoid. -/
theorem one_mul (c : GradedMonoid (degree delta p)) :
    (1 : GradedMonoid (degree delta p)) * c = c := sorry

/-- The degree-zero identity is a right identity on the nonnegative graded monoid. -/
theorem mul_one (c : GradedMonoid (degree delta p)) :
    c * (1 : GradedMonoid (degree delta p)) = c := sorry

/-- Nonnegative homogeneous bivariant composition is associative. -/
theorem mul_assoc (a b c : GradedMonoid (degree delta p)) :
    a * b * c = a * (b * c) := sorry

/-- Nonnegative identity-morphism bivariant classes form a graded monoid. -/
instance instGMonoid : GradedMonoid.GMonoid (degree delta p) where
  one_mul := one_mul delta p
  mul_one := mul_one delta p
  mul_assoc := mul_assoc delta p

/-- The natural-number cast in degree zero for nonnegative Chow cohomology. -/
def natCast (n : ℕ) : degree delta p 0 := n • ChowCohomology.one delta p

/-- The degree-zero natural-number cast sends zero to zero. -/
theorem natCast_zero : natCast delta p 0 = 0 := sorry

/-- The degree-zero natural-number cast respects successors. -/
theorem natCast_succ (n : ℕ) :
    natCast delta p (n + 1) = natCast delta p n + ChowCohomology.one delta p := sorry

/-- The nonnegative grading carries the graded semiring structure. -/
instance instGSemiring : DirectSum.GSemiring (degree delta p) where
  natCast := natCast delta p
  natCast_zero := natCast_zero delta p
  natCast_succ := natCast_succ delta p

/-- The integer cast in degree zero for nonnegative Chow cohomology. -/
def intCast (z : ℤ) : degree delta p 0 := z • ChowCohomology.one delta p

/-- The integer cast agrees with the natural-number cast on natural numbers. -/
theorem intCast_ofNat (n : ℕ) : intCast delta p n = natCast delta p n := sorry

/-- The integer cast has the canonical negative-successor value. -/
theorem intCast_negSucc (n : ℕ) :
    intCast delta p (Int.negSucc n) = -natCast delta p (n + 1) := sorry

/-- The nonnegative grading carries the graded ring structure. -/
instance instGRing : DirectSum.GRing (degree delta p) where
  intCast := intCast delta p
  intCast_ofNat := intCast_ofNat delta p
  intCast_negSucc_ofNat := intCast_negSucc delta p

/-- Nonnegative Chow cohomology has the ring structure induced by finite convolution. -/
instance instRing : Ring (ring delta p) := inferInstance

end AlgebraicGeometry.ChowCohomology.Nonnegative

namespace AlgebraicGeometry.ChowCohomology

/-- The product of the finite-support nonnegative cohomology rings of the components of
an explicit disjoint clopen cover. -/
abbrev completedRing
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] {I : Type v} (U : I → X.left.Opens)
    (hU_cover : iSup U = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hId : ∀ i, U i ≤ (𝟙 X : X ⟶ X).left ⁻¹ᵁ U i) :=
  ∀ i, Nonnegative.ring delta (BivariantClass.ComponentRestriction.over X (U i)).hom

/-- The completed cohomology carrier is the product of its component rings. -/
theorem completedRing_def
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] {I : Type v} (U : I → X.left.Opens)
    (hU_cover : iSup U = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hId : ∀ i, U i ≤ (𝟙 X : X ⟶ X).left ⁻¹ᵁ U i) :
    completedRing delta X U hU_cover hU_disjoint hU_clopen hId =
      (∀ i, Nonnegative.ring delta
        (BivariantClass.ComponentRestriction.over X (U i)).hom) := sorry

/-- For a disjoint clopen cover, completed cohomology is the componentwise completion
of the identity morphism. -/
theorem completedRing_eq_completion
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] {I : Type v} (U : I → X.left.Opens)
    (hU_cover : iSup U = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hId : ∀ i, U i ≤ (𝟙 X : X ⟶ X).left ⁻¹ᵁ U i) :
    completedRing delta X U hU_cover hU_disjoint hU_clopen hId =
      BivariantClass.OpenRestriction.Completion delta (𝟙 X) U U id hId := sorry

/-- Composing the identity completion with itself has the identity-completion carrier. -/
theorem identityCompCompletion_eq
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] {I : Type v} (U : I → X.left.Opens)
    (hId : ∀ i, U i ≤ (𝟙 X : X ⟶ X).left ⁻¹ᵁ U i)
    (hIdComp : ∀ i, U i ≤ ((𝟙 X : X ⟶ X) ≫ 𝟙 X).left ⁻¹ᵁ U i) :
    BivariantClass.OpenRestriction.Completion delta ((𝟙 X) ≫ (𝟙 X))
        U U (id ∘ id) hIdComp =
      BivariantClass.OpenRestriction.Completion delta (𝟙 X) U U id hId := sorry

/-- Componentwise convolution gives completed cohomology its canonical ring structure. -/
instance instRingCompletedRing
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] {I : Type v} (U : I → X.left.Opens)
    (hU_cover : iSup U = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hId : ∀ i, U i ≤ (𝟙 X : X ⟶ X).left ⁻¹ᵁ U i) :
    Ring (completedRing delta X U hU_cover hU_disjoint hU_clopen hId) := inferInstance

/-- Multiplication in completed cohomology is completed composition for the identity. -/
theorem completedRing_mul_eq_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] {I : Type v} (U : I → X.left.Opens)
    (hU_cover : iSup U = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hId : ∀ i, U i ≤ (𝟙 X : X ⟶ X).left ⁻¹ᵁ U i)
    (hIdComp : ∀ i, U i ≤ ((𝟙 X : X ⟶ X) ≫ 𝟙 X).left ⁻¹ᵁ U i)
    (c d : completedRing delta X U hU_cover hU_disjoint hU_clopen hId) :
    Eq.mp (completedRing_eq_completion delta X U hU_cover hU_disjoint hU_clopen hId)
        (c * d) =
      Eq.mp (identityCompCompletion_eq delta X U hId hIdComp)
        (BivariantClass.OpenRestriction.Completion.comp delta (𝟙 X) (𝟙 X)
          U U U id id hId hId hIdComp
          (Eq.mp (completedRing_eq_completion delta X U hU_cover hU_disjoint hU_clopen hId) c)
          (Eq.mp (completedRing_eq_completion delta X U hU_cover hU_disjoint hU_clopen hId) d)) := sorry

end AlgebraicGeometry.ChowCohomology
