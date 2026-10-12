/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris
public import ReasLib.Topology.Sheaf.Cohomology.Spectral
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u v

/- Exercise 111.60.2 (Theorems) (1): Yoneda lemma: natural transformations
`yoneda.obj X ⟶ F` are equivalent to elements of `F.obj (Opposite.op X)`. -/
@[stacks 0EEL] #check
  (CategoryTheory.RepresentablePresheaf.homEquiv :
    ∀ {C : Type u} [Category.{v} C] {X : C} {F : Cᵒᵖ ⥤ Type v},
      (yoneda.obj X ⟶ F) ≃ F.obj (Opposite.op X))

/- Exercise 111.60.2 (Theorems) (2): Mayer–Vietoris: the five-arrow sequence for
module cohomology over a two-open cover of a ringed space is exact. -/
@[stacks 0EEL] #check
  (AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris.sequence_exact :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}}
      [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
      (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (F : X.Modules) (n : ℕ),
      (AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris.sequence U V hUV F n).Exact)

/- Exercise 111.60.2 (Theorems) (3): dimension and cohomology: on a spectral space
of Krull dimension at most `d`, abelian sheaf cohomology vanishes in degrees `q > d`. -/
@[stacks 0EEL] #check
  (TopCat.Sheaf.Cohomology.Spectral.isZero_of_krullDim_le :
    ∀ {X : TopCat.{u}} [SpectralSpace X] (F : X.Sheaf AddCommGrpCat.{u}) (d : ℕ),
      topologicalKrullDim X ≤ d → ∀ {q : ℕ}, d < q →
        IsZero (F.H' q (⊤ : Opens X)))

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
