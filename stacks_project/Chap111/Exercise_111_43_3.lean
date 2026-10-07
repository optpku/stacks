module

public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Exercise 111.43.3

Zariski cohomology of the structure sheaf of the complement of the origin in
affine `d`-space over a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace

/-- The structure morphism of the complement of the origin in affine `d`-space over `k`. -/
abbrev puncturedToBase (d : ℕ) (k : Type u) [Field k] :
    (puncturedOpen (ULift.{u} (Fin d)) k).toScheme ⟶ Spec (CommRingCat.of k) :=
  (puncturedOpen (ULift.{u} (Fin d)) k).ι ≫ toBase (ULift.{u} (Fin d)) k

/-- The structure sheaf of the complement of the origin, as a sheaf of modules. -/
abbrev unitModule (d : ℕ) (k : Type u) [Field k] :
    (puncturedOpen (ULift.{u} (Fin d)) k).toScheme.Modules :=
  SheafOfModules.unit (puncturedOpen (ULift.{u} (Fin d)) k).toScheme.ringCatSheaf

/-- Zariski cohomology of `𝒪_U` on the complement of the origin in `𝔸^d_k`, as a `k`-module. -/
abbrev structureSheafCohomology (d : ℕ) (k : Type u) [Field k] (n : ℕ) : ModuleCat k :=
  Scheme.Hom.cohomology (puncturedToBase d k) (unitModule d k) n

/-- Unfolding of `structureSheafCohomology` as cohomology of the unit module. -/
theorem structureSheafCohomology_def (d : ℕ) (k : Type u) [Field k] (n : ℕ) :
    structureSheafCohomology d k n =
      Scheme.Hom.cohomology (puncturedToBase d k) (unitModule d k) n := sorry

/-- The explicit carrier of `H⁰(U, 𝒪_U)`: zero for `d = 0`, Laurent polynomials for `d = 1`,
and the coordinate ring for `2 ≤ d`. -/
def sectionsModel (d : ℕ) (k : Type u) [Field k] : Type u :=
  match d with
  | 0 => ULift.{u} PUnit
  | 1 => LaurentPolynomial k
  | n + 2 => coordinateRing (ULift.{u} (Fin (n + 2))) k

/-- Additive group structure on `sectionsModel`, by cases on the dimension. -/
instance instAddCommGroupSectionsModel (d : ℕ) (k : Type u) [Field k] :
    AddCommGroup (sectionsModel d k) :=
  match d with
  | 0 => inferInstanceAs (AddCommGroup (ULift.{u} PUnit))
  | 1 => inferInstanceAs (AddCommGroup (LaurentPolynomial k))
  | n + 2 => inferInstanceAs (AddCommGroup (coordinateRing (ULift.{u} (Fin (n + 2))) k))

/-- `k`-module structure on `sectionsModel`, by cases on the dimension. -/
instance instModuleSectionsModel (d : ℕ) (k : Type u) [Field k] :
    Module k (sectionsModel d k) :=
  match d with
  | 0 => inferInstanceAs (Module k (ULift.{u} PUnit))
  | 1 => inferInstanceAs (Module k (LaurentPolynomial k))
  | n + 2 => inferInstanceAs (Module k (coordinateRing (ULift.{u} (Fin (n + 2))) k))

/-- The degree-zero sections model in dimension `0` is a singleton. -/
theorem sectionsModel_zero (k : Type u) [Field k] :
    sectionsModel 0 k = ULift.{u} PUnit := sorry

/-- The degree-zero sections model in dimension `1` is the Laurent polynomial ring. -/
theorem sectionsModel_one (k : Type u) [Field k] :
    sectionsModel 1 k = LaurentPolynomial k := sorry

/-- The degree-zero sections model in dimension at least `2` is the coordinate ring. -/
theorem sectionsModel_of_two_le (d : ℕ) (k : Type u) [Field k] (hd : 2 ≤ d) :
    sectionsModel d k = coordinateRing (ULift.{u} (Fin d)) k := sorry

/-- Strictly negative exponent vectors in `d` coordinates. -/
abbrev negativeExponent (d : ℕ) :=
  {a : Fin d → ℤ // ∀ i, a i < 0}

/-- Finitely supported linear combinations of strictly negative Laurent monomials. -/
abbrev negativeLaurent (d : ℕ) (k : Type u) [Field k] :=
  negativeExponent d →₀ k

/-- Every multiindex in the support of a negative Laurent series is strictly negative in each
coordinate. -/
theorem negativeLaurent_mem_support {d : ℕ} {k : Type u} [Field k]
    (f : negativeLaurent d k) {a : negativeExponent d} (ha : a ∈ f.support) (i : Fin d) :
    a.val i < 0 := sorry

/-- Exercise 111.43.3 (1): `H⁰(U, 𝒪_U)` is the sections model of the complement of the origin
in affine `d`-space over the field `k`. -/
@[stacks 0DAL]
theorem cohomology_zero (d : ℕ) (k : Type u) [Field k] :
    IsIsomorphic (structureSheafCohomology d k 0) (ModuleCat.of k (sectionsModel d k)) := sorry

/-- Exercise 111.43.3 (2): `Hⁿ(U, 𝒪_U)` vanishes for every degree distinct from `0` and `d - 1`. -/
@[stacks 0DAL]
theorem cohomology_isZero_of_ne (d : ℕ) (k : Type u) [Field k] (n : ℕ)
    (hn0 : n ≠ 0) (hntop : n ≠ d.pred) :
    IsZero (structureSheafCohomology d k n) := sorry

/-- Exercise 111.43.3 (3): for `2 ≤ d`, the group `H^{d-1}(U, 𝒪_U)` is the module of strictly
negative Laurent monomials. -/
@[stacks 0DAL]
theorem cohomology_top (d : ℕ) (k : Type u) [Field k] (hd : 2 ≤ d) :
    IsIsomorphic (structureSheafCohomology d k d.pred)
      (ModuleCat.of k (negativeLaurent d k)) := sorry

end AlgebraicGeometry.PuncturedAffineSpace
