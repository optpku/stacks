/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.MayerVietoris
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.LowerShriek
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity

/-! # Cochain and derived Mayer–Vietoris constructions for module sheaves -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Pretriangulated ComplexShape
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing (restrictFunctorComp)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

variable {U V X : AlgebraicSpace S} (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]

/-- Canonical iso from `mapDerivedCategory` of the composite functor to the
composite of the derived functors, specialized to a morphism `g`. -/
def mayerVietorisLowerShriekOfCompIso {W : AlgebraicSpace S} (g : W ⟶ X)
    [Etale g] :
    (ExactFunctor.of (restrictFunctor g ⋙ lowerShriek g)).mapDerivedCategory ≅
      restrictFunctorDerived g ⋙ lowerShriekDerived g :=
  ExactFunctor.MapDerivedCategory.mapIso
      ((exactFunctor X.Modules X.Modules).isoMk (Iso.refl _)) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso (ExactFunctor.of (restrictFunctor g))
      (ExactFunctor.of (lowerShriek g))

/-- Derived `U`-leg comparison in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekιDerivedU (E : ModuleDerived X) :
    (lowerShriekDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) ⟶
      (lowerShriekDerived j).obj ((restrictFunctorDerived j).obj E) :=
  (mayerVietorisLowerShriekOfCompIso (fiberHom j f)).inv.app E ≫
    (ExactFunctor.MapDerivedCategory.map ({ hom := mayerVietorisLowerShriekιNatTransU j f } :
      ExactFunctor.of (restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)) ⟶
        ExactFunctor.of (restrictFunctor j ⋙ lowerShriek j))).app E ≫
    (mayerVietorisLowerShriekOfCompIso j).hom.app E

/-- Derived `V`-leg comparison in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekιDerivedV (E : ModuleDerived X) :
    (lowerShriekDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) ⟶
      (lowerShriekDerived f).obj ((restrictFunctorDerived f).obj E) :=
  (mayerVietorisLowerShriekOfCompIso (fiberHom j f)).inv.app E ≫
    (ExactFunctor.MapDerivedCategory.map ({ hom := mayerVietorisLowerShriekιNatTransV j f } :
      ExactFunctor.of (restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)) ⟶
        ExactFunctor.of (restrictFunctor f ⋙ lowerShriek f))).app E ≫
    (mayerVietorisLowerShriekOfCompIso f).hom.app E

/-- Derived first Mayer–Vietoris arrow in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekιDerived (E : ModuleDerived X) :
    (lowerShriekDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) ⟶
      biprod ((lowerShriekDerived j).obj ((restrictFunctorDerived j).obj E))
        ((lowerShriekDerived f).obj ((restrictFunctorDerived f).obj E)) :=
  biprod.lift (mayerVietorisLowerShriekιDerivedU j f E)
    (-mayerVietorisLowerShriekιDerivedV j f E)

/-- The derived counit of restriction followed by extension by zero along an
étale morphism. -/
def mayerVietorisLowerShriekπDerivedLeg {W : AlgebraicSpace S} (g : W ⟶ X)
    [Etale g] (E : ModuleDerived X) :
    (lowerShriekDerived g).obj ((restrictFunctorDerived g).obj E) ⟶ E :=
  (mayerVietorisLowerShriekOfCompIso g).inv.app E ≫
    (ExactFunctor.MapDerivedCategory.map
      ({ hom := (lowerShriekAdjunction g).counit } :
        ExactFunctor.of (restrictFunctor g ⋙ lowerShriek g) ⟶
          ExactFunctor.id X.Modules)).app E ≫
    (ExactFunctor.MapDerivedCategory.idObjIso X.Modules E).hom

/-- Derived second Mayer–Vietoris arrow in `D(𝒪_X)`. -/
def mayerVietorisLowerShriekπDerived (E : ModuleDerived X) :
    biprod ((lowerShriekDerived j).obj ((restrictFunctorDerived j).obj E))
        ((lowerShriekDerived f).obj ((restrictFunctorDerived f).obj E)) ⟶ E :=
  biprod.desc (mayerVietorisLowerShriekπDerivedLeg j E)
    (mayerVietorisLowerShriekπDerivedLeg f E)

/-- The cochain-level first Mayer–Vietoris arrow. -/
def mayerVietorisLowerShriekCochainι (K : CochainComplex X.Modules ℤ) :
    ((restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)).mapHomologicalComplex
        (up ℤ)).obj K ⟶
      biprod (((restrictFunctor j ⋙ lowerShriek j).mapHomologicalComplex (up ℤ)).obj K)
        (((restrictFunctor f ⋙ lowerShriek f).mapHomologicalComplex (up ℤ)).obj K) :=
  biprod.lift
    ((NatTrans.mapHomologicalComplex (mayerVietorisLowerShriekιNatTransU j f)
        (up ℤ)).app K)
    (-(NatTrans.mapHomologicalComplex (mayerVietorisLowerShriekιNatTransV j f)
        (up ℤ)).app K)

/-- The cochain-level second Mayer–Vietoris arrow. -/
def mayerVietorisLowerShriekCochainπ (K : CochainComplex X.Modules ℤ) :
    biprod (((restrictFunctor j ⋙ lowerShriek j).mapHomologicalComplex (up ℤ)).obj K)
        (((restrictFunctor f ⋙ lowerShriek f).mapHomologicalComplex (up ℤ)).obj K) ⟶ K :=
  biprod.desc
    ((NatTrans.mapHomologicalComplex (lowerShriekAdjunction j).counit (up ℤ)).app K ≫
      (Functor.mapHomologicalComplexIdIso X.Modules (up ℤ)).hom.app K)
    ((NatTrans.mapHomologicalComplex (lowerShriekAdjunction f).counit (up ℤ)).app K ≫
      (Functor.mapHomologicalComplexIdIso X.Modules (up ℤ)).hom.app K)

/-- The short complex of cochain complexes obtained by applying the module-level
Mayer–Vietoris arrows degreewise. -/
def mayerVietorisLowerShriekCochainShortComplex (K : CochainComplex X.Modules ℤ) :
    ShortComplex (CochainComplex X.Modules ℤ) :=
  ShortComplex.mk (mayerVietorisLowerShriekCochainι j f K)
    (mayerVietorisLowerShriekCochainπ j f K) sorry

/-- The cochain-level Mayer–Vietoris sequence is short exact. -/
theorem mayerVietorisLowerShriekCochain_shortExact [IsElementaryDistinguishedSquare j f]
    (K : CochainComplex X.Modules ℤ) :
    (mayerVietorisLowerShriekCochainShortComplex j f K).ShortExact :=
  sorry

/-- The connecting morphism of the Mayer–Vietoris triangle in `D(𝒪_X)`, obtained
from `triangleOfSESδ` of a cochain-level short exact sequence representing `E`. -/
def mayerVietorisLowerShriekδ (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    E ⟶ ((lowerShriekDerived (fiberHom j f)).obj
      ((restrictFunctorDerived (fiberHom j f)).obj E))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.Q.objObjPreimageIso E).inv ≫
    DerivedCategory.triangleOfSESδ h ≫
    ((restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)).mapDerivedCategoryFactors.inv.app
        (DerivedCategory.Q.objPreimage E))⟦(1 : ℤ)⟧' ≫
    ((restrictFunctor (fiberHom j f) ⋙ lowerShriek (fiberHom j f)).mapDerivedCategory.map
        (DerivedCategory.Q.objObjPreimageIso E).hom)⟦(1 : ℤ)⟧' ≫
    (mayerVietorisLowerShriekOfCompIso (fiberHom j f)).hom.app E⟦(1 : ℤ)⟧'

/-- The Mayer–Vietoris distinguished-triangle data of étale lower shriek in
`D(𝒪_X)`. -/
def mayerVietorisLowerShriekTriangle (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    Triangle (ModuleDerived X) :=
  Triangle.mk (mayerVietorisLowerShriekιDerived j f E)
    (mayerVietorisLowerShriekπDerived j f E) (mayerVietorisLowerShriekδ j f E h)

/-- The first vertex of the Mayer–Vietoris triangle is
`j_{U×_X V!} (E|_{U×_X V})`. -/
theorem mayerVietorisLowerShriekTriangle_obj₁ (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    (mayerVietorisLowerShriekTriangle j f E h).obj₁ =
      (lowerShriekDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E) :=
  rfl

/-- The second vertex of the Mayer–Vietoris triangle is
`j_{U!} (E|_U) ⊞ j_{V!} (E|_V)`. -/
theorem mayerVietorisLowerShriekTriangle_obj₂ (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    (mayerVietorisLowerShriekTriangle j f E h).obj₂ =
      biprod ((lowerShriekDerived j).obj ((restrictFunctorDerived j).obj E))
        ((lowerShriekDerived f).obj ((restrictFunctorDerived f).obj E)) :=
  rfl

/-- The third vertex of the Mayer–Vietoris triangle is `E`. -/
theorem mayerVietorisLowerShriekTriangle_obj₃ (E : ModuleDerived X)
    (h : (mayerVietorisLowerShriekCochainShortComplex j f
            (DerivedCategory.Q.objPreimage E)).ShortExact) :
    (mayerVietorisLowerShriekTriangle j f E h).obj₃ = E :=
  rfl

/-- For an elementary distinguished square of algebraic spaces, extension by zero
of the intersection and the two legs gives a distinguished triangle in the derived
category of structure-sheaf modules. -/
theorem mayerVietorisLowerShriek_mem_distTriang {U V X : AlgebraicSpace S}
    (j : U ⟶ X) (f : V ⟶ X) [h : IsElementaryDistinguishedSquare j f]
    (E : ModuleDerived X) :
    -- Local instance justification (search instability): Extract the square's open-immersion certificate because class search for IsOpenImmersion j cannot determine the opposite leg f.
    letI : IsOpenImmersion j := h.isOpenImmersion
    -- Local instance justification (search instability): Extract the square's etale certificate because class search for Etale f cannot determine the opposite leg j.
    letI : Etale f := h.isEtale
    mayerVietorisLowerShriekTriangle j f E
        (mayerVietorisLowerShriekCochain_shortExact j f
          (DerivedCategory.Q.objPreimage E)) ∈
      distTriang (ModuleDerived X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
