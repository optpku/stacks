module

public import stacks_project.Chap42.Remark_42_34_7_Cutoff
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.SumProduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Cutoff

/-- The mixed product of two cutoff degrees of total natural degree `n`, valued in
the relative bivariant group of degree `n`. The both-ambient branch is empty once
`p + q ≤ n`, and is defined as the pointwise zero class. -/
def mulTerm
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n) (i j : ℕ) (hij : i + j = n)
    (c : Cutoff δ f p (i : ℤ)) (d : Cutoff δ f q (j : ℤ)) :
    BivariantClass δ f (n : ℤ) :=
  if hi : (i : ℤ) < p then
    if hj : (j : ℤ) < q then
      pointwiseZero δ f (n : ℤ)
    else
      Nonnegative.castGrading δ
        ((Nat.cast_add i j).symm.trans (congrArg (fun k : ℕ ↦ (k : ℤ)) hij))
        (ambientMulRelative δ f i j (toAmbient δ f hi c) (toRelative δ f hj d))
  else if hj : (j : ℤ) < q then
    Nonnegative.castGrading δ
      ((Nat.cast_add i j).symm.trans (congrArg (fun k : ℕ ↦ (k : ℤ)) hij))
      (relativeMulAmbient δ f i j (toRelative δ f hi c) (toAmbient δ f hj d))
  else
    Nonnegative.castGrading δ
      ((Nat.cast_add i j).symm.trans (congrArg (fun k : ℕ ↦ (k : ℤ)) hij))
      (relativeMul δ f i j (toRelative δ f hi c) (toRelative δ f hj d))

/-- If the first cutoff degree is ambient and the second is relative, `mulTerm` is
the ambient-relative product. -/
theorem mulTerm_of_fst_lt
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n) (i j : ℕ) (hij : i + j = n)
    (c : Cutoff δ f p (i : ℤ)) (d : Cutoff δ f q (j : ℤ))
    (hi : (i : ℤ) < p) (hj : ¬(j : ℤ) < q) :
    mulTerm δ f p q n hn i j hij c d =
      Nonnegative.castGrading δ
        ((Nat.cast_add i j).symm.trans (congrArg (fun k : ℕ ↦ (k : ℤ)) hij))
        (ambientMulRelative δ f i j (toAmbient δ f hi c) (toRelative δ f hj d)) :=
  sorry

/-- Finite antidiagonal mixed convolution of two cutoff families into a relative
class of degree `n ≥ p + q`. -/
def mixedMul
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n)
    (c : (i : ℕ) → Cutoff δ f p (i : ℤ))
    (d : (j : ℕ) → Cutoff δ f q (j : ℤ)) :
    BivariantClass δ f (n : ℤ) :=
  @Finset.sum _ (BivariantClass δ f (n : ℤ))
    (pointwiseAddCommGroup δ f (n : ℤ)).toAddCommMonoid
    (Finset.antidiagonal n).attach
    (fun ij ↦ mulTerm δ f p q n hn ij.1.1 ij.1.2
      (Finset.mem_antidiagonal.mp ij.2) (c ij.1.1) (d ij.1.2))

/-- `mixedMul` is the finite antidiagonal sum of mixed cutoff products. -/
theorem mixedMul_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n)
    (c : (i : ℕ) → Cutoff δ f p (i : ℤ))
    (d : (j : ℕ) → Cutoff δ f q (j : ℤ)) :
    mixedMul δ f p q n hn c d =
      @Finset.sum _ (BivariantClass δ f (n : ℤ))
        (pointwiseAddCommGroup δ f (n : ℤ)).toAddCommMonoid
        (Finset.antidiagonal n).attach
        (fun ij ↦ mulTerm δ f p q n hn ij.1.1 ij.1.2
          (Finset.mem_antidiagonal.mp ij.2) (c ij.1.1) (d ij.1.2)) := sorry

/-- In the original high-degree range, the existing mixed convolution is exactly
the relative coefficient of the corrected sum-cutoff product. Both sides use
the same three cap pairings; the ambient-ambient branch is arithmetically empty. -/
theorem mixedMul_eq_familyMul
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (f : Z ⟶ X) [IsClosedImmersion f.left]
    (p q n : ℕ) (hn : p + q ≤ n)
    (c : Family δ f p) (d : Family δ f q) :
    mixedMul δ f p q n hn c d =
      toRelative δ f (not_lt.mpr (Nat.cast_le.mpr hn))
        (familyMul δ f p q c d n) := sorry

end AlgebraicGeometry.BivariantClass.Cutoff

namespace AlgebraicGeometry.LocalizedChern

open BivariantClass BivariantClass.Cutoff

/-- The mixed cutoff Chern series whose degrees below `p` are ambient and whose
degrees at least `p` are relative localized classes. -/
def cutoffChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p n : ℕ)
    (ambient : ChowCohomology.Nonnegative.degree δ X.hom n)
    (localized : BivariantClass δ i (n : ℤ)) :
    Cutoff δ i p (n : ℤ) :=
  if h : (n : ℤ) < p then ofAmbient δ i h ambient else ofRelative δ i h localized

/-- Below the cutoff, `cutoffChernClass` recovers the ambient class. -/
theorem cutoffChernClass_apply_lt
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p n : ℕ)
    (ambient : ChowCohomology.Nonnegative.degree δ X.hom n)
    (localized : BivariantClass δ i (n : ℤ))
    (h : (n : ℤ) < p) :
    toAmbient δ i h (cutoffChernClass δ i p n ambient localized) = ambient := sorry

/-- At or above the cutoff, `cutoffChernClass` recovers the relative localized class. -/
theorem cutoffChernClass_apply_ge
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {Z X : Over S} [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left] (p n : ℕ)
    (ambient : ChowCohomology.Nonnegative.degree δ X.hom n)
    (localized : BivariantClass δ i (n : ℤ))
    (h : ¬(n : ℤ) < p) :
    toRelative δ i h (cutoffChernClass δ i p n ambient localized) = localized := sorry

end AlgebraicGeometry.LocalizedChern
