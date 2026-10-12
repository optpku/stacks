/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Quotient.Head
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Localization

/-!
# Polynomial presentations of affine blowup charts

This leaf owns the quotient presentation associated to a distinguished center
element `a : I` and a family of remaining center generators.  The generic API
is independent of a finite tuple; `AffineBlowupChart.Presentation.Tuple` is
the ergonomic specialization for a family indexed by `Fin (r + 1)`.
-/

@[expose] public section

noncomputable section

universe u v

open MvPolynomial
open scoped AffineBlowupChart

namespace AffineBlowupChart.Presentation

variable {R : Type u} [CommRing R]
variable {ι : Type v}

/-! ## A distinguished generator and an arbitrary family -/

/-- The relation `a X i - x i` used in a polynomial presentation of the chart away from `a`. -/
@[stacks 0G8S "affine blowup chart presentation relation"]
def relation {I : Ideal R} (a : I) (x : ι → I) (i : ι) : MvPolynomial ι R :=
  C a.1 * X i - C (x i).1

/-- The ideal of presentation relations `a X i - x i`. -/
@[stacks 0G8S "affine blowup chart presentation relation ideal"]
def relationIdeal {I : Ideal R} (a : I) (x : ι → I) : Ideal (MvPolynomial ι R) :=
  Ideal.span (Set.range (relation a x))

/-- Each displayed presentation relation belongs to the presentation relation ideal. -/
@[stacks 0G8S "affine blowup chart presentation relation membership"]
theorem relation_mem_relationIdeal {I : Ideal R} (a : I) (x : ι → I) (i : ι) :
    relation a x i ∈ relationIdeal a x := sorry

/-- The polynomial quotient defined by the relations `a X i = x i`. -/
@[stacks 0G8S "affine blowup chart presentation quotient"]
abbrev Quotient {I : Ideal R} (a : I) (x : ι → I) :=
  MvPolynomial ι R ⧸ relationIdeal a x

/-- The chart fraction corresponding to a member of the chosen generator family. -/
@[stacks 0G8S "affine blowup chart presentation generator"]
noncomputable def generator {I : Ideal R} (a : I) (x : ι → I) (i : ι) : R[I / a] :=
  AffineBlowupChart.basicFraction I a (x i)

/-- Polynomial evaluation at the chosen chart fractions. -/
@[stacks 0G8S "affine blowup chart presentation polynomial map"]
noncomputable def toChart {I : Ideal R} (a : I) (x : ι → I) :
    MvPolynomial ι R →ₐ[R] R[I / a] :=
  MvPolynomial.aeval (generator a x)

/-- Each presentation relation vanishes under `toChart`. -/
@[stacks 0G8S "affine blowup chart presentation relation vanishing"]
theorem relation_toChart {I : Ideal R} (a : I) (x : ι → I) (i : ι) :
    toChart a x (relation a x i) = 0 := sorry

/-- Every member of the presentation relation ideal vanishes under `toChart`. -/
@[stacks 0G8S "affine blowup chart presentation relation ideal vanishing"]
theorem toChart_eq_zero_of_mem_relationIdeal {I : Ideal R} (a : I) (x : ι → I)
    (p : MvPolynomial ι R) (hp : p ∈ relationIdeal a x) :
    toChart a x p = 0 := sorry

/-- The canonical quotient map from the polynomial presentation to the affine blowup chart. -/
@[stacks 0G8S "affine blowup chart presentation map"]
noncomputable def map {I : Ideal R} (a : I) (x : ι → I) :
    Quotient a x →ₐ[R] R[I / a] :=
  Ideal.Quotient.liftₐ (relationIdeal a x) (toChart a x)
    (toChart_eq_zero_of_mem_relationIdeal a x)

/-- The presentation map on a polynomial quotient class is polynomial evaluation in the chart. -/
@[stacks 0G8S "affine blowup chart presentation map on quotient representatives", simp]
theorem map_mk {I : Ideal R} (a : I) (x : ι → I) (p : MvPolynomial ι R) :
    map a x (Ideal.Quotient.mk (relationIdeal a x) p) = toChart a x p := sorry

/-- The presentation map preserves the canonical copy of the base ring. -/
@[stacks 0G8S "affine blowup chart presentation map on scalars", simp]
theorem map_algebraMap {I : Ideal R} (a : I) (x : ι → I) (r : R) :
    map a x (Ideal.Quotient.mk (relationIdeal a x) (MvPolynomial.C r)) =
      AffineBlowupChart.algebraMap I a r := sorry

/-- The presentation map sends a variable class to its prescribed chart fraction. -/
@[stacks 0G8S "affine blowup chart presentation map on variables", simp]
theorem map_X {I : Ideal R} (a : I) (x : ι → I) (i : ι) :
    map a x (Ideal.Quotient.mk (relationIdeal a x) (X i)) = generator a x i := sorry

/-- If `a` together with the chosen family generates the center, the presentation map is
surjective. -/
@[stacks 0G8S "affine blowup chart presentation map surjective"]
theorem map_surjective {I : Ideal R} (a : I) (x : ι → I)
    (hI : I ≤ Ideal.span (Set.insert a.1 (Set.range fun i : ι ↦ (x i : R)))) :
    Function.Surjective (map a x) := sorry

/-- Membership in the kernel of the presentation map is annihilation by a power of the
distinguished parameter. -/
@[stacks 0G8S "affine blowup chart presentation kernel power criterion"]
theorem map_ker_iff {I : Ideal R} (a : I) (x : ι → I) (z : Quotient a x) :
    z ∈ RingHom.ker (map a x).toRingHom ↔
      ∃ n : ℕ, (algebraMap R (Quotient a x) a.1) ^ n * z = 0 := sorry

/-- The kernel of the presentation map is the primary component of the principal parameter
ideal. -/
@[stacks 0G8S "affine blowup chart presentation primary-component kernel"]
theorem map_ker_eq_primaryComponent {I : Ideal R} (a : I) (x : ι → I) :
    RingHom.ker (map a x).toRingHom =
      (Ideal.span ({algebraMap R (Quotient a x) a.1} : Set (Quotient a x))).primaryComponent
        (Quotient a x) := sorry

/-! ## The finite tuple specialization -/

namespace Tuple

variable {r : ℕ} (f : Fin (r + 1) → R)

/-- The tail of a finite family, viewed in the ideal generated by the whole family. -/
@[stacks 0G8S "tail generators of a tuple affine blowup presentation"]
def tail : Fin r → Ideal.span (Set.range f) :=
  fun i ↦ ⟨f i.succ, Ideal.subset_span ⟨i.succ, rfl⟩⟩

/-- Coercing a tuple-tail generator recovers the corresponding successor entry. -/
@[stacks 0G8S "tuple affine blowup presentation tail coercion", simp]
theorem coe_tail (i : Fin r) : (tail f i : R) = f i.succ := sorry

/-- The quotient presentation attached to a finite family with its first entry distinguished. -/
@[stacks 0G8S "tuple affine blowup presentation quotient"]
abbrev Quotient :=
  AffineBlowupChart.Presentation.Quotient (Ideal.spanRangeFirst f) (tail f)

/-- The canonical map from the tuple presentation to its affine blowup chart. -/
@[stacks 0G8S "tuple affine blowup presentation map"]
noncomputable abbrev map : Quotient f →ₐ[R]
    @affineBlowupChart R _ (Ideal.span (Set.range f)) (Ideal.spanRangeFirst f) :=
  AffineBlowupChart.Presentation.map (Ideal.spanRangeFirst f) (tail f)

/-- The tuple presentation map is surjective because the first entry together with the tail is
the original family of generators. -/
@[stacks 0G8S "tuple affine blowup presentation map surjective"]
theorem map_surjective : Function.Surjective (map f) := sorry

/-- Membership in the kernel of the tuple presentation map is annihilation by a power of its
first entry. -/
@[stacks 0G8S "tuple affine blowup presentation kernel power criterion"]
theorem map_ker_iff (z : Quotient f) :
    z ∈ RingHom.ker (map f).toRingHom ↔
      ∃ n : ℕ, (algebraMap R (Quotient f) (f 0)) ^ n * z = 0 := sorry

/-- The kernel of the tuple presentation map is the primary component of its first parameter. -/
@[stacks 0G8S "tuple affine blowup presentation primary-component kernel"]
theorem map_ker_eq_primaryComponent :
    RingHom.ker (map f).toRingHom =
      (Ideal.span ({algebraMap R (Quotient f) (f 0)} : Set (Quotient f))).primaryComponent
        (Quotient f) := sorry

end Tuple

end AffineBlowupChart.Presentation
