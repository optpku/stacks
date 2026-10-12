/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_10_5_Gamma
public import stacks_project.Chap75.Lemma_75_10_5_Sequence

/-!
# Mayer–Vietoris triangle for derived global sections of algebraic spaces

Lemma 75.10.5: along an elementary distinguished square of algebraic spaces,
abelian-valued derived global sections of an unbounded complex yield a
distinguished triangle, a long exact cohomology sequence, and both constructions
are functorial in the complex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.ComposableArrows

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 75.10.5 (1). Let `S` be a scheme. Let `(U ⊂ X, V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. For an object `E` of `D(𝒪_X)`
the triangle
`RΓ(X, E) ⟶ RΓ(U, E) ⊕ RΓ(V, E) ⟶ RΓ(U ×_X V, E) ⟶ RΓ(X, E)⟦1⟧`
is distinguished in `D(Ab)`. -/
@[stacks 0CRS]
theorem mayerVietorisGamma_mem_distTriang {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f]
    [(restrictFunctor (fiberHom j f)).Additive]
    [(restrictFunctor j).Additive] [(restrictFunctor f).Additive]
    [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)]
    [PreservesFiniteLimits (restrictFunctor f)]
    [PreservesFiniteColimits (restrictFunctor f)]
    (E : ModuleDerived X) :
    mayerVietorisGammaTriangle j f E ∈ distTriang (DerivedCategory AddCommGrpCat.{u}) :=
  sorry

/-- Lemma 75.10.5 (2). Let `S` be a scheme. Let `(U ⊂ X, V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. For an object `E` of `D(𝒪_X)`
and each `n : ℤ`, the cohomology segment
`H^n(X, E) ⟶ H^n(U, E) ⊕ H^n(V, E) ⟶ H^n(U ×_X V, E) ⟶ H^{n+1}(X, E) ⟶
H^{n+1}(U, E) ⊕ H^{n+1}(V, E)`
of the Mayer–Vietoris triangle is exact. -/
@[stacks 0CRS]
theorem mayerVietorisGammaCohomology_exact {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f]
    [(restrictFunctor (fiberHom j f)).Additive]
    [(restrictFunctor j).Additive] [(restrictFunctor f).Additive]
    [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)]
    [PreservesFiniteLimits (restrictFunctor f)]
    [PreservesFiniteColimits (restrictFunctor f)]
    (E : ModuleDerived X) (n : ℤ) :
    (mayerVietorisGammaCohomologyArrows j f E n).Exact :=
  sorry

/-- Lemma 75.10.5 (3). Let `S` be a scheme. Let `(U ⊂ X, V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. The construction of the
distinguished triangle and the long exact cohomology sequence is functorial in
`E`: triangle maps are the corresponding `RΓ(φ)` maps, identities and composition
are preserved, and the three cohomology arrows are natural in `φ`. -/
@[stacks 0CRS]
theorem mayerVietorisGamma_functorial {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f]
    [(restrictFunctor (fiberHom j f)).Additive]
    [(restrictFunctor j).Additive] [(restrictFunctor f).Additive]
    [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
    [PreservesFiniteLimits (restrictFunctor j)]
    [PreservesFiniteColimits (restrictFunctor j)]
    [PreservesFiniteLimits (restrictFunctor f)]
    [PreservesFiniteColimits (restrictFunctor f)]
    (E : ModuleDerived X) :
    (mayerVietorisGammaTriangleMap j f (𝟙 E) =
        triangleMorphismId (mayerVietorisGammaTriangle j f E) ∧
      ∀ {E' E'' : ModuleDerived X} (φ : E ⟶ E') (ψ : E' ⟶ E''),
        mayerVietorisGammaTriangleMap j f (φ ≫ ψ) =
          TriangleMorphism.comp (mayerVietorisGammaTriangleMap j f φ)
            (mayerVietorisGammaTriangleMap j f ψ)) ∧
      ∀ {E' : ModuleDerived X} (φ : E ⟶ E') (n : ℤ),
        (mayerVietorisGammaCohomologyι j f E n ≫
            biprod.map (cohomologyAb_map ((restrictFunctorDerived j).map φ) n)
              (cohomologyAb_map ((restrictFunctorDerived f).map φ) n) =
          cohomologyAb_map φ n ≫ mayerVietorisGammaCohomologyι j f E' n) ∧
        (mayerVietorisGammaCohomologyπ j f E n ≫
            cohomologyAb_map ((restrictFunctorDerived (fiberHom j f)).map φ) n =
          biprod.map (cohomologyAb_map ((restrictFunctorDerived j).map φ) n)
            (cohomologyAb_map ((restrictFunctorDerived f).map φ) n) ≫
            mayerVietorisGammaCohomologyπ j f E' n) ∧
        (mayerVietorisGammaCohomologyδ j f E n ≫ cohomologyAb_map φ (n + 1) =
          cohomologyAb_map ((restrictFunctorDerived (fiberHom j f)).map φ) n ≫
            mayerVietorisGammaCohomologyδ j f E' n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
