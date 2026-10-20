module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris.GlobalSections

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.ComposableArrows

universe u

/- Lemma 75.10.5. Abelian-valued derived global sections along an elementary
distinguished square form a distinguished triangle, yielding a functorial long
exact hypercohomology sequence. -/
@[stacks 0CRS] #check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisGamma_mem_distTriang :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f]
    (E : ModuleDerived X),
    mayerVietorisGammaTriangle j f E ∈ distTriang (DerivedCategory AddCommGrpCat.{u}))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisGammaCohomology_exact :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f]
    (E : ModuleDerived X) (n : ℤ),
    (mayerVietorisGammaCohomologyArrows j f E n).Exact)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisGamma_functorial :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f]
    (E : ModuleDerived X),
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
            mayerVietorisGammaCohomologyδ j f E' n))

