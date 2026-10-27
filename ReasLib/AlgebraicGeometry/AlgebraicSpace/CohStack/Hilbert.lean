/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TensorPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical.TensorPower
public import ReasLib.RingTheory.Polynomial.IntegerValued

/-!
# Hilbert-polynomial family of an invertible sheaf

The derived family `n ↦ L^{⊗ n}` on `ULift ℤ`, and the numerical locus
`Coh^{P,L}_{X/B}` of coherent families with prescribed integral-twist invariants.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The index type `ℤ` at the universe of numerical invariants of `CohStack`. -/
abbrev hilbertIndex : Type u :=
  ULift.{u, 0} ℤ

/-- The derived family `n ↦ L^{⊗ n}` on `hilbertIndex`, as integral tensor powers
of the degree-zero single complex of an invertible `𝒪_X`-module. -/
def hilbertFamily (L : X.Modules) [isInvertibleObject L] :
    hilbertIndex.{u} → ModuleDerived X :=
  fun n ↦ ModuleDerived.tensorPowerInt
    ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj L) n.down

/-- Evaluating `hilbertFamily L` at `⟨n⟩` recovers the integral derived
tensor power of `L[0]`. -/
theorem hilbertFamily_apply (L : X.Modules) [isInvertibleObject L] (n : ℤ) :
    hilbertFamily L (⟨n⟩ : hilbertIndex.{u}) =
      ModuleDerived.tensorPowerInt
        ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj L) n :=
  sorry

/-- Integral derived tensor powers of an invertible `𝒪_X`-module remain perfect. -/
theorem isPerfect_hilbertFamily (L : X.Modules) [isInvertibleObject L]
    (n : hilbertIndex.{u}) :
    ModuleDerived.IsPerfect (hilbertFamily L n) :=
  sorry

/-- An object of `CohStack f` has Hilbert polynomial `P` with respect to `L` if
`χ(X_t, F_t ⊗ L_t^{⊗ n}) = P n` at every integer and every point of the test
scheme. -/
def Obj.HasHilbertPolynomial {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ) : Prop :=
  ∀ (n : ℤ) (t : Points (ofOver x.σ.left)),
    x.eulerChar (hilbertFamily L (⟨n⟩ : hilbertIndex.{u})) t = P n

/-- The Hilbert-polynomial condition unpacks as the pointwise Euler-characteristic
identity. -/
theorem Obj.HasHilbertPolynomial_iff {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ) :
    x.HasHilbertPolynomial L P ↔
      ∀ (n : ℤ) (t : Points (ofOver x.σ.left)),
        x.eulerChar (hilbertFamily L (⟨n⟩ : hilbertIndex.{u})) t = P n :=
  sorry

/-- The object property of `CohStack f` cut out by Hilbert polynomial `P` with
respect to `L`, as the numerical locus of `hilbertFamily L`. -/
abbrev hilbert (f : X ⟶ B) [FinitePresentation f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) : ObjectProperty (Obj f) :=
  numerical f (hilbertFamily L) (fun n ↦ P n.down)

/-- Membership in `hilbert f L P` is `HasHilbertPolynomial`. -/
theorem mem_hilbert {f : X ⟶ B} [FinitePresentation f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) (x : Obj f) :
    hilbert f L P x ↔ x.HasHilbertPolynomial L P :=
  sorry

/-- The full subcategory of `CohStack f` on objects with Hilbert polynomial `P`
with respect to `L`. -/
abbrev Hilbert (f : X ⟶ B) [FinitePresentation f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) :=
  Numerical f (hilbertFamily L) (fun n ↦ P n.down)

/-- Package an object of `CohStack f` in the Hilbert locus as an object of
`Hilbert f L P`. -/
def Hilbert.of {f : X ⟶ B} [FinitePresentation f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) (x : Obj f) (hx : hilbert f L P x) :
    Hilbert f L P :=
  Numerical.of (hilbertFamily L) (fun n ↦ P n.down) x hx

/-- The underlying `CohStack` object of `Hilbert.of` is the supplied object. -/
theorem Hilbert.of_obj {f : X ⟶ B} [FinitePresentation f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) (x : Obj f) (hx : hilbert f L P x) :
    (Hilbert.of L P x hx).obj = x :=
  sorry

/-- The Hilbert-polynomial substack as a category fibred in groupoids over
`Over S`. -/
abbrev toGroupoidsHilbert (f : X ⟶ B) [FinitePresentation f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) :=
  toGroupoidsNumerical f (hilbertFamily L) (fun n ↦ P n.down)
    (isPerfect_hilbertFamily L)

/-- The inclusion `Coh^{P,L}_{X/B} ⟶ Coh_{X/B}` of categories fibred in groupoids
over `Over S`. -/
abbrev Hilbert.ι (f : X ⟶ B) [FinitePresentation f] (L : X.Modules)
    [isInvertibleObject L] (P : ℤ → ℤ) :
    toGroupoidsHilbert f L P ⟶ toGroupoids f :=
  Numerical.ι f (hilbertFamily L) (fun n ↦ P n.down) (isPerfect_hilbertFamily L)

/-- Membership in an integer-valued rational Hilbert locus means that the polynomial
agrees with every integral-twist Euler characteristic at every test-scheme point. -/
theorem mem_hilbert_iff (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (L : X.Modules) [isInvertibleObject L] (p : Polynomial ℚ)
    (hp : p.IsIntegerValued) (x : Obj f) :
    hilbert f L hp.evalInt x ↔
      ∀ (n : ℤ) (t : Points (ofOver x.σ.left)),
        p.eval (n : ℚ) = (x.eulerChar (hilbertFamily L ⟨n⟩) t : ℚ) := sorry

/-- The inclusion of the locus with prescribed integral-twist Euler characteristics
of an invertible module is an open immersion. -/
instance instOpenImmersion_ι_hilbert (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ) :
    CohStack.OpenImmersion (Hilbert.ι f L P) := sorry

/-- At every test-scheme point, the integral-twist Euler characteristics agree at
all integers with a unique integer-valued rational polynomial. -/
theorem existsUnique_hilbertPolynomial (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (L : X.Modules) [isInvertibleObject L] (x : Obj f)
    (t : Points (ofOver x.σ.left)) :
    ∃! p : Polynomial ℚ, p.IsIntegerValued ∧
      ∀ n : ℤ, p.eval (n : ℚ) = (x.eulerChar (hilbertFamily L ⟨n⟩) t : ℚ) := sorry

/-- A coherent family over a test scheme with a point belongs to at most one
integer-valued rational Hilbert-polynomial locus. -/
theorem eq_of_mem_hilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (L : X.Modules) [isInvertibleObject L] (p q : Polynomial ℚ)
    (hp : p.IsIntegerValued) (hq : q.IsIntegerValued) (x : Obj f)
    (hT : Nonempty (Points (ofOver x.σ.left))) (hxp : hilbert f L hp.evalInt x)
    (hxq : hilbert f L hq.evalInt x) : p = q := sorry

/-- The point locus where every integral-twist Euler characteristic equals a
prescribed integer-valued function. -/
def Obj.hilbertLocus {f : X ⟶ B} [FinitePresentation f] (x : Obj f)
    (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ) :
    Set (Points (ofOver x.σ.left)) :=
  {t | ∀ n : ℤ, x.eulerChar (hilbertFamily L ⟨n⟩) t = P n}

/-- A family belongs to a Hilbert locus exactly when its point locus is the whole
test scheme. -/
theorem Obj.hilbertLocus_eq_univ_iff {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ) :
    x.hilbertLocus L P = Set.univ ↔ hilbert f L P x := sorry

/-- Every locus of prescribed integral-twist Euler characteristics is open and
closed in the point space of the test scheme. -/
theorem Obj.isClopen_hilbertLocus {f : X ⟶ B} [FinitePresentation f] [Separated f]
    (x : Obj f) (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ) :
    IsClopen (x.hilbertLocus L P) := sorry

/-- Hilbert point loci pull back along every morphism of coherent families. -/
theorem Obj.hilbertLocus_natural {f : X ⟶ B} [FinitePresentation f]
    {x y : Obj f} (α : Hom x y) (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ) :
    x.hilbertLocus L P =
      Points.map (ofOverMap α.base.left) ⁻¹' y.hilbertLocus L P := sorry

/-- Distinct integer-valued rational polynomials have disjoint Hilbert point loci. -/
theorem Obj.hilbertLocus_pairwiseDisjoint {f : X ⟶ B} [FinitePresentation f]
    (x : Obj f) (L : X.Modules) [isInvertibleObject L] :
    Pairwise (fun p q : {p : Polynomial ℚ // p.IsIntegerValued} ↦
      Disjoint (x.hilbertLocus L p.property.evalInt)
        (x.hilbertLocus L q.property.evalInt)) := sorry

/-- The Hilbert point loci indexed by all integer-valued rational polynomials cover
the entire point space of every test scheme. -/
theorem Obj.iUnion_hilbertLocus {f : X ⟶ B} [FinitePresentation f] [Separated f]
    (x : Obj f) (L : X.Modules) [isInvertibleObject L] :
    (⋃ p : {p : Polynomial ℚ // p.IsIntegerValued},
      x.hilbertLocus L p.property.evalInt) = Set.univ := sorry

/-- A coherent family over a connected test scheme belongs to a Hilbert locus for
some integer-valued rational polynomial. -/
theorem exists_mem_hilbert_of_isConnected (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (L : X.Modules) [isInvertibleObject L] (x : Obj f)
    [ConnectedSpace x.σ.left.left] :
    ∃ p : Polynomial ℚ, ∃ hp : p.IsIntegerValued, hilbert f L hp.evalInt x := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
