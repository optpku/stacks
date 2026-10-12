/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Composition
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex.Cohomology

/-!
# Derived-category maps of enriched Hom complexes

This module is the stable owner of the explicit morphisms in `D(R)` induced by enriched
Hom-complex maps. Abstract localization and resolution-independent `RHom` constructions remain in
`HomComplex.Derived`.
-/

@[expose] public section

noncomputable section

universe u v w h z

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedCategory.HomComplex

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DA : DifferentialGradedCategory.{u, v, h} R A]
variable [DB : DifferentialGradedCategory.{u, w, h} R B]

/-- The enriched Hom complex, regarded as an object of the derived category of `R`-modules. -/
@[stacks 0CS6 "enriched Hom complex in the derived category"]
abbrev derived (X Y : A) [HasDerivedCategory (ModuleCat.{h} R)] :
    DerivedCategory (ModuleCat.{h} R) :=
  DerivedCategory.Q.obj (homComplex X Y)

/-- A DG functor induces a concrete morphism between enriched Hom objects in `D(R)`. -/
@[stacks 0CS6 "derived Hom-complex comparison induced by a DG functor"]
def derivedMap (F : DgFunctor R A B) (X Y : A)
    [HasDerivedCategory (ModuleCat.{h} R)] :
    derived X Y ⟶ derived (F.obj X) (F.obj Y) :=
  DerivedCategory.Q.map (map F X Y)

/-- The derived Hom-complex map of the identity DG functor is the identity. -/
@[simp, stacks 0CS6 "identity law for derived DG Hom maps"]
theorem derivedMap_id (X Y : A) [HasDerivedCategory (ModuleCat.{h} R)] :
    derivedMap (DgFunctor.id R A) X Y = 𝟙 (derived X Y) := sorry

/-- Derived Hom-complex maps compose in the same order as DG functors. -/
@[stacks 0CS6 "composition law for derived DG Hom maps"]
theorem derivedMap_comp {C : Type z}
    [DC : DifferentialGradedCategory.{u, z, h} R C]
    (G : DgFunctor R B C) (F : DgFunctor R A B) (X Y : A)
    [HasDerivedCategory (ModuleCat.{h} R)] :
    derivedMap (DgFunctor.comp G F) X Y =
      derivedMap F X Y ≫ derivedMap G (F.obj X) (F.obj Y) := sorry

/-- A DG functor followed by a closed target morphism induces a morphism of Hom objects in
`D(R)`. -/
@[stacks 0CS6 "postcomposed derived Hom-complex comparison"]
def derivedMapPostcomp (F : DgFunctor R A B) (X Y : A)
    {Z : B} (g : CompHom (F.obj Y) Z)
    [HasDerivedCategory (ModuleCat.{h} R)] :
    derived X Y ⟶ derived (F.obj X) Z :=
  DerivedCategory.Q.map (mapPostcomp F X Y g)

/-- Source naturality of the induced morphism between Hom objects in `D(R)`. -/
theorem derivedMap_naturality_source (F : DgFunctor R A B)
    [HasDerivedCategory (ModuleCat.{h} R)]
    {X X' Y : A} (f : CompHom X' X) :
    DerivedCategory.Q.map (precomp f) ≫ derivedMap F X' Y =
      derivedMap F X Y ≫
        DerivedCategory.Q.map (precomp (F.mapCompHom f)) := sorry

/-- Target naturality of the induced morphism between Hom objects in `D(R)`. -/
theorem derivedMap_naturality_target (F : DgFunctor R A B)
    [HasDerivedCategory (ModuleCat.{h} R)]
    {X Y Y' : A} (g : CompHom Y Y') :
    DerivedCategory.Q.map (postcomp g) ≫ derivedMap F X Y' =
      derivedMap F X Y ≫
        DerivedCategory.Q.map (postcomp (F.mapCompHom g)) := sorry

/-- The postcomposed derived map is contravariantly natural in the source. -/
theorem derivedMapPostcomp_naturality_source (F : DgFunctor R A B)
    [HasDerivedCategory (ModuleCat.{h} R)]
    {X X' Y : A} {Z : B} (f : CompHom X' X)
    (g : CompHom (F.obj Y) Z) :
    DerivedCategory.Q.map (precomp f) ≫ derivedMapPostcomp F X' Y g =
      derivedMapPostcomp F X Y g ≫
        DerivedCategory.Q.map (precomp (F.mapCompHom f)) := sorry

/-- Target naturality of the postcomposed derived map is composition of its closed target
morphism. -/
theorem derivedMapPostcomp_naturality_target (F : DgFunctor R A B)
    [HasDerivedCategory (ModuleCat.{h} R)]
    {X Y Y' : A} {Z : B} (f : CompHom Y Y')
    (g : CompHom (F.obj Y') Z) :
    DerivedCategory.Q.map (postcomp f) ≫ derivedMapPostcomp F X Y' g =
      derivedMapPostcomp F X Y (CompHom.comp (F.mapCompHom f) g) := sorry

/-- Further postcomposition is absorbed into the closed morphism defining the derived map. -/
theorem derivedMapPostcomp_postcomp (F : DgFunctor R A B)
    [HasDerivedCategory (ModuleCat.{h} R)]
    (X Y : A) {Z Z' : B} (f : CompHom (F.obj Y) Z)
    (g : CompHom Z Z') :
    derivedMapPostcomp F X Y f ≫ DerivedCategory.Q.map (postcomp g) =
      derivedMapPostcomp F X Y (CompHom.comp f g) := sorry

/-- Applying derived cohomology to `derivedMap` gives the ordinary cohomology map of the
explicit Hom-complex morphism. -/
theorem derivedMap_cohomology (F : DgFunctor R A B)
    [HasDerivedCategory (ModuleCat.{h} R)] (X Y : A) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{h} R) n).map
          (derivedMap F X Y) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{h} R) n).hom.app
          (homComplex (F.obj X) (F.obj Y)) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{h} R) n).hom.app
          (homComplex X Y) ≫ cohomologyMap F X Y n := sorry

/-- Applying derived cohomology to `derivedMapPostcomp` gives the cohomology map of its explicit
postcomposed Hom-complex morphism. -/
theorem derivedMapPostcomp_cohomology (F : DgFunctor R A B)
    [HasDerivedCategory (ModuleCat.{h} R)] (X Y : A)
    {Z : B} (g : CompHom (F.obj Y) Z) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{h} R) n).map
          (derivedMapPostcomp F X Y g) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{h} R) n).hom.app
          (homComplex (F.obj X) Z) =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{h} R) n).hom.app
          (homComplex X Y) ≫ cohomologyMapPostcomp F X Y g n := sorry

end DifferentialGradedCategory.HomComplex
