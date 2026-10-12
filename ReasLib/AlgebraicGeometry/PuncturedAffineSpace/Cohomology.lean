/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections

/-!
# Cohomology of finite-dimensional punctured affine space

The structure sheaf on affine space punctured at the origin has explicit
degree-zero and positive-degree cohomology models.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedAffineSpace

/-- The structure morphism from affine `d`-space punctured at the origin to the field `k`. -/
abbrev puncturedToBase (d : ℕ) (k : Type u) [Field k] :
    (puncturedOpen (ULift.{u} (Fin d)) k).toScheme ⟶ Spec (CommRingCat.of k) :=
  (puncturedOpen (ULift.{u} (Fin d)) k).ι ≫ toBase (ULift.{u} (Fin d)) k

/-- The structure sheaf on punctured affine `d`-space, regarded as a sheaf of modules. -/
abbrev unitModule (d : ℕ) (k : Type u) [Field k] :
    (puncturedOpen (ULift.{u} (Fin d)) k).toScheme.Modules :=
  SheafOfModules.unit (puncturedOpen (ULift.{u} (Fin d)) k).toScheme.ringCatSheaf

/-- The `k`-module of degree-`n` cohomology of the structure sheaf on punctured affine space. -/
abbrev structureSheafCohomology (d : ℕ) (k : Type u) [Field k] (n : ℕ) : ModuleCat k :=
  Scheme.Hom.cohomology (puncturedToBase d k) (unitModule d k) n

/-- Degree-zero sections are zero in dimension zero, Laurent polynomials in dimension one,
and the polynomial coordinate ring in dimensions at least two. -/
def sectionsModel (d : ℕ) (k : Type u) [Field k] : Type u :=
  match d with
  | 0 => ULift.{u} PUnit
  | 1 => LaurentPolynomial k
  | n + 2 => coordinateRing (ULift.{u} (Fin (n + 2))) k

/-- The additive group structure on the degree-zero sections model. -/
instance instAddCommGroupSectionsModel (d : ℕ) (k : Type u) [Field k] :
    AddCommGroup (sectionsModel d k) :=
  match d with
  | 0 => inferInstanceAs (AddCommGroup (ULift.{u} PUnit))
  | 1 => inferInstanceAs (AddCommGroup (LaurentPolynomial k))
  | n + 2 => inferInstanceAs (AddCommGroup (coordinateRing (ULift.{u} (Fin (n + 2))) k))

/-- The scalar action of `k` on the degree-zero sections model. -/
instance instModuleSectionsModel (d : ℕ) (k : Type u) [Field k] :
    Module k (sectionsModel d k) :=
  match d with
  | 0 => inferInstanceAs (Module k (ULift.{u} PUnit))
  | 1 => inferInstanceAs (Module k (LaurentPolynomial k))
  | n + 2 => inferInstanceAs (Module k (coordinateRing (ULift.{u} (Fin (n + 2))) k))

/-- In dimension zero the degree-zero sections model is a singleton. -/
theorem sectionsModel_zero (k : Type u) [Field k] :
    sectionsModel 0 k = ULift.{u} PUnit := sorry

/-- In dimension one the degree-zero sections model is the Laurent polynomial ring. -/
theorem sectionsModel_one (k : Type u) [Field k] :
    sectionsModel 1 k = LaurentPolynomial k := sorry

/-- In dimensions at least two the degree-zero sections model is the coordinate ring. -/
theorem sectionsModel_of_two_le (d : ℕ) (k : Type u) [Field k] (hd : 2 ≤ d) :
    sectionsModel d k = coordinateRing (ULift.{u} (Fin d)) k := sorry

/-- Exponent vectors strictly negative in every coordinate. -/
abbrev negativeExponent (d : ℕ) :=
  {a : Fin d → ℤ // ∀ i, a i < 0}

/-- Finitely supported `k`-linear combinations of strictly negative Laurent monomials. -/
abbrev negativeLaurent (d : ℕ) (k : Type u) [Field k] :=
  negativeExponent d →₀ k

/-- The degree-zero cohomology of punctured affine `d`-space is its explicit sections model. -/
theorem cohomology_zero (d : ℕ) (k : Type u) [Field k] :
    IsIsomorphic (structureSheafCohomology d k 0) (ModuleCat.of k (sectionsModel d k)) := sorry

/-- Cohomology outside degrees zero and `d - 1` vanishes. -/
theorem cohomology_isZero_of_ne (d : ℕ) (k : Type u) [Field k] (n : ℕ)
    (hn0 : n ≠ 0) (hntop : n ≠ d.pred) :
    IsZero (structureSheafCohomology d k n) := sorry

/-- In dimension at least two, cohomology in degree `d - 1` consists of the strictly
negative Laurent monomials. -/
theorem cohomology_top (d : ℕ) (k : Type u) [Field k] (hd : 2 ≤ d) :
    IsIsomorphic (structureSheafCohomology d k d.pred)
      (ModuleCat.of k (negativeLaurent d k)) := sorry

end AlgebraicGeometry.PuncturedAffineSpace
