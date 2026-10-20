module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Composition
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex

/-!
# Cohomology maps of enriched Hom complexes

This module is the stable owner of the cohomology maps induced by the chain-level enriched Hom
API. It also provides a controlled cycle representative for constructions that genuinely require
strict data; invariant downstream APIs should depend on its specification theorem.
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

/-- The map induced by a DG functor on degree-`n` cohomology of enriched Hom complexes. -/
@[stacks 0CS6 "DG functor map on enriched Hom cohomology"]
noncomputable def cohomologyMap (F : DgFunctor R A B) (X Y : A) (n : ℤ) :
    (homComplex X Y).homology n ⟶
      (homComplex (F.obj X) (F.obj Y)).homology n :=
  HomologicalComplex.homologyMap (map F X Y) n

/-- Contravariant source naturality remains visible after taking Hom-complex cohomology. -/
@[stacks 0CS6 "source naturality on enriched Hom cohomology"]
theorem cohomologyMap_naturality_source (F : DgFunctor R A B)
    {X X' Y : A} (f : CompHom X' X) (n : ℤ) :
    HomologicalComplex.homologyMap (precomp f) n ≫ cohomologyMap F X' Y n =
      cohomologyMap F X Y n ≫
        HomologicalComplex.homologyMap (precomp (F.mapCompHom f)) n := sorry

/-- Covariant target naturality remains visible after taking Hom-complex cohomology. -/
@[stacks 0CS6 "target naturality on enriched Hom cohomology"]
theorem cohomologyMap_naturality_target (F : DgFunctor R A B)
    {X Y Y' : A} (g : CompHom Y Y') (n : ℤ) :
    HomologicalComplex.homologyMap (postcomp g) n ≫ cohomologyMap F X Y' n =
      cohomologyMap F X Y n ≫
        HomologicalComplex.homologyMap (postcomp (F.mapCompHom g)) n := sorry

/-- The cohomology map of the identity DG functor is the identity. -/
@[simp, stacks 0CS6 "identity law for DG Hom cohomology maps"]
theorem cohomologyMap_id (X Y : A) (n : ℤ) :
    cohomologyMap (DgFunctor.id R A) X Y n = 𝟙 _ := sorry

/-- Cohomology maps induced by DG functors compose in the same order as the functors. -/
@[stacks 0CS6 "composition law for DG Hom cohomology maps"]
theorem cohomologyMap_comp {C : Type z}
    [DC : DifferentialGradedCategory.{u, z, h} R C]
    (G : DgFunctor R B C) (F : DgFunctor R A B) (X Y : A) (n : ℤ) :
    cohomologyMap (DgFunctor.comp G F) X Y n =
      cohomologyMap F X Y n ≫ cohomologyMap G (F.obj X) (F.obj Y) n := sorry

/-- Cohomology of a DG functor map followed by postcomposition with a closed morphism. -/
@[stacks 0CS6 "DG functor map followed by postcomposition on Hom cohomology"]
noncomputable def cohomologyMapPostcomp (F : DgFunctor R A B) (X Y : A)
    {Z : B} (g : CompHom (F.obj Y) Z) (n : ℤ) :
    (homComplex X Y).homology n ⟶ (homComplex (F.obj X) Z).homology n :=
  HomologicalComplex.homologyMap (mapPostcomp F X Y g) n

/-- The postcomposed cohomology map is contravariantly natural in the source. -/
@[stacks 0CS6 "source naturality of postcomposed Hom cohomology"]
theorem cohomologyMapPostcomp_naturality_source (F : DgFunctor R A B)
    {X X' Y : A} {Z : B} (f : CompHom X' X)
    (g : CompHom (F.obj Y) Z) (n : ℤ) :
    HomologicalComplex.homologyMap (precomp f) n ≫
        cohomologyMapPostcomp F X' Y g n =
      cohomologyMapPostcomp F X Y g n ≫
        HomologicalComplex.homologyMap (precomp (F.mapCompHom f)) n := sorry

/-- Target naturality of the postcomposed cohomology map is composition of its closed
postcomposition morphism. -/
@[stacks 0CS6 "target naturality of postcomposed Hom cohomology"]
theorem cohomologyMapPostcomp_naturality_target (F : DgFunctor R A B)
    {X Y Y' : A} {Z : B} (f : CompHom Y Y')
    (g : CompHom (F.obj Y') Z) (n : ℤ) :
    HomologicalComplex.homologyMap (postcomp f) n ≫
        cohomologyMapPostcomp F X Y' g n =
      cohomologyMapPostcomp F X Y (CompHom.comp (F.mapCompHom f) g) n := sorry

/-- Further postcomposition is absorbed by the closed morphism defining the cohomology map. -/
@[stacks 0CS6 "postcomposition law for Hom cohomology"]
theorem cohomologyMapPostcomp_postcomp (F : DgFunctor R A B)
    (X Y : A) {Z Z' : B} (f : CompHom (F.obj Y) Z)
    (g : CompHom Z Z') (n : ℤ) :
    cohomologyMapPostcomp F X Y f n ≫
        HomologicalComplex.homologyMap (postcomp g) n =
      cohomologyMapPostcomp F X Y (CompHom.comp f g) n := sorry

/-- A controlled cycle representative of a class in the cohomology of an enriched Hom complex.
The representative is chosen through the explicit kernel-quotient homology model of
`ModuleCat`; downstream data should use `cycleOfHomology_spec` rather than inspect the choice. -/
@[stacks 0CS6 "controlled representative of enriched Hom cohomology"]
def cycleOfHomology (X Y : A) (n : ℤ) (x : (homComplex X Y).homology n) :
    (homComplex X Y).cycles n :=
  ((homComplex X Y).sc n).moduleCatCyclesIso.inv
    (Quotient.out (((homComplex X Y).sc n).moduleCatHomologyIso.hom x))

/-- The controlled cycle representative projects to its original Hom-complex cohomology
class. -/
@[simp, stacks 0CS6 "cohomology representative projection"]
theorem cycleOfHomology_spec (X Y : A) (n : ℤ)
    (x : (homComplex X Y).homology n) :
    ModuleCat.Hom.hom ((homComplex X Y).homologyπ n)
      (cycleOfHomology X Y n x) = x := sorry

end DifferentialGradedCategory.HomComplex
