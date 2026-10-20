module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap108.Lemma_108_4_9_TensorPower
public import stacks_project.Chap108.Situation_108_4_7_Numerical_invariants_Substack

/-!
# Hilbert-polynomial family of an invertible sheaf

The derived family `n ↦ L^{⊗ n}` on `ULift ℤ`, and the numerical locus
`Coh^{P,L}_{X/B}` of Situation 108.4.7 specialized to that family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory CategoryTheory.ObjectProperty

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

/-- The degree-zero single complex of an invertible `𝒪_X`-module is perfect. -/
theorem isPerfect_single_of_isInvertible (L : X.Modules) [isInvertibleObject L] :
    ModuleDerived.IsPerfect
      ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj L) :=
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

end AlgebraicGeometry.AlgebraicSpace.CohStack
