module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import stacks_project.Chap20.Proposition_20_20_7_Grothendieck
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u v w

/- Exercise 111.60.2 (Theorems) (1): Yoneda lemma: natural transformations
`yoneda.obj X ⟶ F` are equivalent to elements of `F.obj (Opposite.op X)`. -/
@[stacks 0EEL] #check
  (CategoryTheory.yonedaEquiv :
    ∀ {C : Type u} [Category.{v} C] {X : C} {F : Cᵒᵖ ⥤ Type v},
      (yoneda.obj X ⟶ F) ≃ F.obj (Opposite.op X))

/- Exercise 111.60.2 (Theorems) (2): Mayer–Vietoris: the five-arrow sheaf-cohomology
sequence of a Mayer–Vietoris square is exact; this includes the two-open cover. -/
@[stacks 0EEL] #check
  (CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact :
    ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
      [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
      [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
      (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
      (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁),
      (S.sequence F n₀ n₁ h).Exact)

/- Exercise 111.60.2 (Theorems) (3): dimension and cohomology: on a Noetherian space of
Krull dimension at most `d`, abelian sheaf cohomology vanishes in degrees `p > d`. -/
@[stacks 0EEL] #check
  (CategoryTheory.Sheaf.isZero_higherCohomology_of_noetherianSpace_of_topologicalKrullDim_le :
    ∀ {X : TopCat.{u}} [NoetherianSpace X]
      [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
      [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})] (d : ℕ),
      topologicalKrullDim X ≤ d →
        ∀ (F : X.Sheaf AddCommGrpCat.{u}) {p : ℕ}, d < p →
          IsZero (F.H' p (⊤ : Opens X)))

/- Exercise 111.60.2 (Theorems) (4): Hilbert polynomial: Euler characteristics of canonical
twists of a coherent module on `P^n` over a field form a numerical polynomial. -/
@[stacks 0EEL] #check
  (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial_isNumericalPolynomial :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent],
      IsNumericalPolynomial
        (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial k n ℱ))

/- Exercise 111.60.2 (Theorems) (5): duality for projective space: `H^n(P^n_R, 𝒪(d))` is
the `R`-linear dual of the homogeneous piece of degree `-n - 1 - d`. -/
@[stacks 0EEL] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_top :
    ∀ (R : Type u) [CommRing R] (n : ℕ), 0 < n → ∀ (d : ℤ),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) n)
        (ModuleCat.of R
          (AlgebraicGeometry.ProjectiveSpace.topCohomologyDual R n d)))
