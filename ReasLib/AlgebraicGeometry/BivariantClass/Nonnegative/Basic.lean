module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.FiniteSum

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Nonnegative

/-- Insert a homogeneous bivariant class into its nonnegative degree. -/
def single
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℕ) (c : BivariantClass delta f (p : ℤ)) :
    Nonnegative delta f :=
  -- Local instance justification (defeq pin): pin the direct sum to its specified pointwise additive family.
  letI : ∀ q : ℕ, AddCommMonoid (BivariantClass delta f (q : ℤ)) :=
    fun q ↦ (pointwiseAddCommGroup delta f (q : ℤ)).toAddCommMonoid
  DirectSum.of (fun q : ℕ ↦ BivariantClass delta f (q : ℤ)) p c

/-- The finite sum of nonnegative graded bivariant classes. -/
def sum
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {ι : Type*} (s : Finset ι) (c : ι → Nonnegative delta f) :
    Nonnegative delta f :=
  -- Local instance justification (defeq pin): pin the direct sum to its specified pointwise additive family.
  letI : ∀ q : ℕ, AddCommMonoid (BivariantClass delta f (q : ℤ)) :=
    fun q ↦ (pointwiseAddCommGroup delta f (q : ℤ)).toAddCommMonoid
  ∑ a ∈ s, c a

/-- Integer scaling of a nonnegative graded bivariant class. -/
def zsmul
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (n : ℤ) (c : Nonnegative delta f) : Nonnegative delta f :=
  -- Local instance justification (defeq pin): pin the direct sum to its specified pointwise additive family.
  letI : ∀ q : ℕ, AddCommGroup (BivariantClass delta f (q : ℤ)) :=
    fun q ↦ pointwiseAddCommGroup delta f (q : ℤ)
  n • c

/-- The coefficient of a homogeneous insertion is the transported class at the matching
degree and the pointwise-zero class at every other degree. -/
theorem single_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℕ) (c : BivariantClass delta f (p : ℤ)) (q : ℕ) :
    single delta f p c q =
      if h : p = q then h ▸ c else pointwiseZero delta f (q : ℤ) := sorry

/-- A coefficient of a finite graded sum is the finite pointwise sum of the coefficients. -/
theorem sum_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) {ι : Type*} (s : Finset ι) (c : ι → Nonnegative delta f) (q : ℕ) :
    sum delta f s c q = pointwiseSum delta f (q : ℤ) s (fun a ↦ c a q) := sorry

/-- A coefficient of an integer-scaled graded class is its pointwise integer scaling. -/
theorem zsmul_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (n : ℤ) (c : Nonnegative delta f) (q : ℕ) :
    zsmul delta f n c q = pointwiseZsmul delta f (q : ℤ) (c q) n := sorry

end AlgebraicGeometry.BivariantClass.Nonnegative
