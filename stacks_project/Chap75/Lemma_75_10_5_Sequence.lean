/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import stacks_project.Chap75.Lemma_75_10_2_Sequence
public import stacks_project.Chap75.Lemma_75_10_5_Gamma

/-!
# Mayer–Vietoris triangle of abelian-valued derived global sections

An elementary distinguished square `(j : U ⟶ X, f : V ⟶ X)` determines a triangle
in `D(Ab.{u})` whose vertices are `RΓ(X, E)`, `RΓ(U, E|_U) ⊞ RΓ(V, E|_V)`, and
`RΓ(U ×_X V, E|_{U ×_X V})`, obtained by applying abelian-valued `RΓ(X, -)` to the
étale-pushforward triangle of Lemma 75.10.2 and conjugating by Leray isos.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Functor CategoryTheory.Pretriangulated
open CategoryTheory.ComposableArrows ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U V X : AlgebraicSpace S}
variable (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
variable [IsElementaryDistinguishedSquare j f]
variable [(restrictFunctor (fiberHom j f)).Additive]
variable [(restrictFunctor j).Additive] [(restrictFunctor f).Additive]
variable [PreservesFiniteLimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteColimits (restrictFunctor (fiberHom j f))]
variable [PreservesFiniteLimits (restrictFunctor j)]
variable [PreservesFiniteColimits (restrictFunctor j)]
variable [PreservesFiniteLimits (restrictFunctor f)]
variable [PreservesFiniteColimits (restrictFunctor f)]

/-- Additivity comparison identifying `RΓ(X, A ⊞ B)` with `RΓ(X, A) ⊞ RΓ(X, B)`. -/
def mayerVietorisGammaBiprodIso (E : ModuleDerived X) :
    (moduleDerivedGlobalSectionsAb X).obj
        (biprod ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E))
          ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E))) ≅
      biprod
        ((moduleDerivedGlobalSectionsAb X).obj
          ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E)))
        ((moduleDerivedGlobalSectionsAb X).obj
          ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E))) where
  hom :=
    biprodComparison (moduleDerivedGlobalSectionsAb X)
      ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E))
      ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E))
  inv :=
    biprodComparison' (moduleDerivedGlobalSectionsAb X)
      ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E))
      ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Identification of `RΓ(X, Rj_* (E|_U) ⊞ Rf_* (E|_V))` with
`RΓ(U, E|_U) ⊞ RΓ(V, E|_V)` by additivity and the two Leray isos. -/
def mayerVietorisGammaObj₂Iso (E : ModuleDerived X) :
    (moduleDerivedGlobalSectionsAb X).obj
        (biprod ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E))
          ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E))) ≅
      biprod
        ((moduleDerivedGlobalSectionsAb U).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedGlobalSectionsAb V).obj ((restrictFunctorDerived f).obj E)) :=
  mayerVietorisGammaBiprodIso j f E ≪≫
    biprod.mapIso
      ((derivedGammaPushforwardIso j).app ((restrictFunctorDerived j).obj E))
      ((derivedGammaPushforwardIso f).app ((restrictFunctorDerived f).obj E))

/-- The first Mayer–Vietoris arrow `RΓ(X, E) ⟶ RΓ(U, E|_U) ⊞ RΓ(V, E|_V)`. -/
def mayerVietorisGammaι (E : ModuleDerived X) :
    (moduleDerivedGlobalSectionsAb X).obj E ⟶
      biprod
        ((moduleDerivedGlobalSectionsAb U).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedGlobalSectionsAb V).obj ((restrictFunctorDerived f).obj E)) :=
  (moduleDerivedGlobalSectionsAb X).map (mayerVietorisPushforwardιDerived j f E) ≫
    (mayerVietorisGammaObj₂Iso j f E).hom

/-- The second Mayer–Vietoris arrow
`RΓ(U, E|_U) ⊞ RΓ(V, E|_V) ⟶ RΓ(U ×_X V, E|_{U ×_X V})`. -/
def mayerVietorisGammaπ (E : ModuleDerived X) :
    biprod
        ((moduleDerivedGlobalSectionsAb U).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedGlobalSectionsAb V).obj ((restrictFunctorDerived f).obj E)) ⟶
      (moduleDerivedGlobalSectionsAb (Limits.pullback j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  (mayerVietorisGammaObj₂Iso j f E).inv ≫
    (moduleDerivedGlobalSectionsAb X).map (mayerVietorisPushforwardπDerived j f E) ≫
      ((derivedGammaPushforwardIso (fiberHom j f)).app
        ((restrictFunctorDerived (fiberHom j f)).obj E)).hom

/-- The connecting morphism
`RΓ(U ×_X V, E|_{U ×_X V}) ⟶ RΓ(X, E)⟦1⟧`. -/
def mayerVietorisGammaδ (E : ModuleDerived X) :
    (moduleDerivedGlobalSectionsAb (Limits.pullback j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) ⟶
      ((moduleDerivedGlobalSectionsAb X).obj E)⟦(1 : ℤ)⟧ :=
  ((derivedGammaPushforwardIso (fiberHom j f)).app
      ((restrictFunctorDerived (fiberHom j f)).obj E)).inv ≫
    (moduleDerivedGlobalSectionsAb X).map (mayerVietorisPushforwardδ j f E) ≫
      (commShiftIso (moduleDerivedGlobalSectionsAb X) (1 : ℤ)).hom.app E

/-- The Mayer–Vietoris distinguished-triangle data of abelian-valued `RΓ` along an
elementary distinguished square. -/
def mayerVietorisGammaTriangle (E : ModuleDerived X) :
    Triangle (DerivedCategory AddCommGrpCat.{u}) :=
  Triangle.mk (mayerVietorisGammaι j f E) (mayerVietorisGammaπ j f E)
    (mayerVietorisGammaδ j f E)

/-- The first vertex is `RΓ(X, E)`. -/
theorem mayerVietorisGammaTriangle_obj₁ (E : ModuleDerived X) :
    (mayerVietorisGammaTriangle j f E).obj₁ =
      (moduleDerivedGlobalSectionsAb X).obj E :=
  rfl

/-- The second vertex is `RΓ(U, E|_U) ⊞ RΓ(V, E|_V)`. -/
theorem mayerVietorisGammaTriangle_obj₂ (E : ModuleDerived X) :
    (mayerVietorisGammaTriangle j f E).obj₂ =
      biprod
        ((moduleDerivedGlobalSectionsAb U).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedGlobalSectionsAb V).obj ((restrictFunctorDerived f).obj E)) :=
  rfl

/-- The third vertex is `RΓ(U ×_X V, E|_{U ×_X V})`. -/
theorem mayerVietorisGammaTriangle_obj₃ (E : ModuleDerived X) :
    (mayerVietorisGammaTriangle j f E).obj₃ =
      (moduleDerivedGlobalSectionsAb (Limits.pullback j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  rfl

/-- `mayerVietorisGammaι` is the first morphism of `mayerVietorisGammaTriangle`. -/
theorem mayerVietorisGammaTriangle_mor₁ (E : ModuleDerived X) :
    (mayerVietorisGammaTriangle j f E).mor₁ = mayerVietorisGammaι j f E :=
  rfl

/-- `mayerVietorisGammaπ` is the second morphism of `mayerVietorisGammaTriangle`. -/
theorem mayerVietorisGammaTriangle_mor₂ (E : ModuleDerived X) :
    (mayerVietorisGammaTriangle j f E).mor₂ = mayerVietorisGammaπ j f E :=
  rfl

/-- `mayerVietorisGammaδ` is the connecting morphism of `mayerVietorisGammaTriangle`. -/
theorem mayerVietorisGammaTriangle_mor₃ (E : ModuleDerived X) :
    (mayerVietorisGammaTriangle j f E).mor₃ = mayerVietorisGammaδ j f E :=
  rfl

/-- The morphism of abelian-valued Mayer–Vietoris triangles induced by a map in `D(𝒪_X)`. -/
def mayerVietorisGammaTriangleMap {E E' : ModuleDerived X} (φ : E ⟶ E') :
    TriangleMorphism (mayerVietorisGammaTriangle j f E)
      (mayerVietorisGammaTriangle j f E') :=
  Triangle.homMk _ _
    ((moduleDerivedGlobalSectionsAb X).map φ)
    (biprod.map
      ((moduleDerivedGlobalSectionsAb U).map ((restrictFunctorDerived j).map φ))
      ((moduleDerivedGlobalSectionsAb V).map ((restrictFunctorDerived f).map φ)))
    ((moduleDerivedGlobalSectionsAb (Limits.pullback j f)).map
      ((restrictFunctorDerived (fiberHom j f)).map φ))
    sorry sorry sorry

/-- The first component of `mayerVietorisGammaTriangleMap` is `RΓ(X, φ)`. -/
theorem mayerVietorisGammaTriangleMap_hom₁ {E E' : ModuleDerived X} (φ : E ⟶ E') :
    (mayerVietorisGammaTriangleMap j f φ).hom₁ =
      (moduleDerivedGlobalSectionsAb X).map φ :=
  rfl

/-- The second component of `mayerVietorisGammaTriangleMap` is the biproduct of
`RΓ(U, φ|_U)` and `RΓ(V, φ|_V)`. -/
theorem mayerVietorisGammaTriangleMap_hom₂ {E E' : ModuleDerived X} (φ : E ⟶ E') :
    (mayerVietorisGammaTriangleMap j f φ).hom₂ =
      biprod.map
        ((moduleDerivedGlobalSectionsAb U).map ((restrictFunctorDerived j).map φ))
        ((moduleDerivedGlobalSectionsAb V).map ((restrictFunctorDerived f).map φ)) :=
  rfl

/-- The third component of `mayerVietorisGammaTriangleMap` is
`RΓ(U ×_X V, φ|_{U ×_X V})`. -/
theorem mayerVietorisGammaTriangleMap_hom₃ {E E' : ModuleDerived X} (φ : E ⟶ E') :
    (mayerVietorisGammaTriangleMap j f φ).hom₃ =
      (moduleDerivedGlobalSectionsAb (Limits.pullback j f)).map
        ((restrictFunctorDerived (fiberHom j f)).map φ) :=
  rfl

/-- Homology of the second Mayer–Vietoris vertex identifies with the biproduct of the
two cohomologies. -/
def mayerVietorisGammaCohomologyBiprodIso (E : ModuleDerived X) (n : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((mayerVietorisGammaTriangle j f E).obj₂) ≅
      biprod
        (cohomologyAb U ((restrictFunctorDerived j).obj E) n)
        (cohomologyAb V ((restrictFunctorDerived f).obj E) n) where
  hom :=
    biprodComparison (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n)
      ((moduleDerivedGlobalSectionsAb U).obj ((restrictFunctorDerived j).obj E))
      ((moduleDerivedGlobalSectionsAb V).obj ((restrictFunctorDerived f).obj E))
  inv :=
    biprodComparison' (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n)
      ((moduleDerivedGlobalSectionsAb U).obj ((restrictFunctorDerived j).obj E))
      ((moduleDerivedGlobalSectionsAb V).obj ((restrictFunctorDerived f).obj E))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Degree-`n` cohomology of the first Mayer–Vietoris arrow. -/
def mayerVietorisGammaCohomologyι (E : ModuleDerived X) (n : ℤ) :
    cohomologyAb X E n ⟶
      biprod
        (cohomologyAb U ((restrictFunctorDerived j).obj E) n)
        (cohomologyAb V ((restrictFunctorDerived f).obj E) n) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map (mayerVietorisGammaι j f E) ≫
    (mayerVietorisGammaCohomologyBiprodIso j f E n).hom

/-- Degree-`n` cohomology of the second Mayer–Vietoris arrow. -/
def mayerVietorisGammaCohomologyπ (E : ModuleDerived X) (n : ℤ) :
    biprod
        (cohomologyAb U ((restrictFunctorDerived j).obj E) n)
        (cohomologyAb V ((restrictFunctorDerived f).obj E) n) ⟶
      cohomologyAb (Limits.pullback j f) ((restrictFunctorDerived (fiberHom j f)).obj E) n :=
  (mayerVietorisGammaCohomologyBiprodIso j f E n).inv ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map (mayerVietorisGammaπ j f E)

/-- The connecting map `H^n(U ×_X V, E) ⟶ H^{n+1}(X, E)` of the Mayer–Vietoris triangle. -/
def mayerVietorisGammaCohomologyδ (E : ModuleDerived X) (n : ℤ) :
    cohomologyAb (Limits.pullback j f) ((restrictFunctorDerived (fiberHom j f)).obj E) n ⟶
      cohomologyAb X E (n + 1) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
    (mayerVietorisGammaTriangle j f E) n (n + 1) rfl

/-- The five-term cohomology arrow
`H^n(X, E) ⟶ H^n(U, E|_U) ⊕ H^n(V, E|_V) ⟶ H^n(U ×_X V, E) ⟶ H^{n+1}(X, E) ⟶
H^{n+1}(U, E|_U) ⊕ H^{n+1}(V, E|_V)`,
with biproduct vertices identified by `mayerVietorisGammaCohomologyBiprodIso`. -/
def mayerVietorisGammaCohomologyArrows (E : ModuleDerived X) (n : ℤ) :
    ComposableArrows AddCommGrpCat.{u} 4 :=
  mk₄ (mayerVietorisGammaCohomologyι j f E n)
    (mayerVietorisGammaCohomologyπ j f E n)
    (mayerVietorisGammaCohomologyδ j f E n)
    (mayerVietorisGammaCohomologyι j f E (n + 1))

/-- The last arrow of the five-term cohomology sequence is `ι` in degree `n + 1`. -/
theorem mayerVietorisGammaCohomologyArrows_map₃ (E : ModuleDerived X) (n : ℤ) :
    (mayerVietorisGammaCohomologyArrows j f E n).map' 3 4 =
      mayerVietorisGammaCohomologyι j f E (n + 1) :=
  rfl

/-- Homology of the Mayer–Vietoris triangle as a six-term composable arrow. -/
def mayerVietorisGammaHomologyArrows₅ (E : ModuleDerived X) (n : ℤ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceComposableArrows₅
    (mayerVietorisGammaTriangle j f E) n (n + 1) rfl

/-- The six-term cohomology arrow of the Mayer–Vietoris triangle, with biproduct vertices
identified by `mayerVietorisGammaCohomologyBiprodIso`. -/
def mayerVietorisGammaCohomologyArrows₅ (E : ModuleDerived X) (n : ℤ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  mk₅ (mayerVietorisGammaCohomologyι j f E n)
    (mayerVietorisGammaCohomologyπ j f E n)
    (mayerVietorisGammaCohomologyδ j f E n)
    (mayerVietorisGammaCohomologyι j f E (n + 1))
    (mayerVietorisGammaCohomologyπ j f E (n + 1))

/-- Transport of the triangle homology sequence onto the source-facing biproduct
cohomology vertices. -/
def mayerVietorisGammaCohomologyArrows₅Iso (E : ModuleDerived X) (n : ℤ) :
    mayerVietorisGammaHomologyArrows₅ j f E n ≅
      mayerVietorisGammaCohomologyArrows₅ j f E n :=
  isoMk₅
    (Iso.refl _)
    (mayerVietorisGammaCohomologyBiprodIso j f E n)
    (Iso.refl _)
    (Iso.refl _)
    (mayerVietorisGammaCohomologyBiprodIso j f E (n + 1))
    (Iso.refl _)
    sorry sorry sorry sorry sorry

/-- Naturality of the three Mayer–Vietoris cohomology arrows in a morphism of `D(𝒪_X)`. -/
theorem mayerVietorisGammaCohomology_natural {E E' : ModuleDerived X}
    (φ : E ⟶ E') (n : ℤ) :
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
