/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import stacks_project.Chap75.Lemma_75_13_4_Sites

/-!
# Exact derived pullback along ε

The morphism ε of 75.4.0.1 is the commutative small Zariski-to-étale restriction
`commSmallEtaleToZariski`. Because it is flat, module pullback is exact and
induces a functor on unbounded derived categories of module sheaves.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite.Hom
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- The standard derived-category structure on modules over a lifted small
commutative ringed site. -/
noncomputable instance smallCommRingedSite_hasDerivedCategory
    (τ : StandardTopology) (S : Scheme.{u}) :
    HasDerivedCategory (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite τ S)) :=
  moduleCat_hasDerivedCategory.{u + 1, u + 1, u, u + 1} (smallCommRingedSite τ S)

/-- Modules over a lifted small commutative ringed site carry the canonical
tensor product of commutative ringed-site modules. -/
noncomputable instance smallCommRingedSite_monoidalCategory
    (τ : StandardTopology) (S : Scheme.{u}) :
    MonoidalCategory (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite τ S)) :=
  moduleMonoidalCategory.{u + 1, u, u + 1} (StandardSmall.commStructureSheaf τ S)

/-- The tensor product on modules over a lifted small commutative ringed site is
additive in each variable. -/
instance smallCommRingedSite_monoidalPreadditive
    (τ : StandardTopology) (S : Scheme.{u}) :
    MonoidalPreadditive (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite τ S)) :=
  (monoidalPreadditive.{u + 1, u, u + 1} :
    MonoidalPreadditive
      (ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (StandardTopology.Small.topology τ S)
        (StandardSmall.commStructureSheaf τ S)))

/-- The total tensor product of complexes of modules over a lifted small
commutative ringed site exists. -/
instance smallCommRingedSite_hasMapBifunctor
    (τ : StandardTopology) (S : Scheme.{u})
    (K L : CochainComplex
      (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite τ S)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (RingedSite.ModuleCat.{u + 1} (smallCommRingedSite τ S)))
      (up ℤ) :=
  moduleCategoryHasMapBifunctor.{u + 1, u, u + 1}
    (StandardSmall.commStructureSheaf τ S) K L

/-- Unbounded derived tensor products exist on modules over a lifted small
commutative ringed site. -/
instance smallCommRingedSite_hasDerivedTensor
    (τ : StandardTopology) (S : Scheme.{u}) :
    DerivedCategory.DerivedTensor.Has
      (C := RingedSite.ModuleCat.{u + 1} (smallCommRingedSite τ S)) :=
  moduleCategoryHasDerivedTensor.{u + 1, u, u + 1}
    (StandardSmall.commStructureSheaf τ S)

/-- Exact derived pullback along the commutative presentation of ε from
75.4.0.1. -/
noncomputable abbrev commSmallEtaleToZariskiDerived (X : Scheme.{u}) :
    ModuleDerived.{u + 1} (smallCommRingedSite .zariski X) ⥤
      ModuleDerived.{u + 1} (smallCommRingedSite .etale X) :=
  (IsFlat.exactPullback (commSmallEtaleToZariski X)).mapDerivedCategory

/-- Exact derived pullback along `commSmallEtaleToZariski` is the derived functor
of the bundled exact module pullback. -/
theorem commSmallEtaleToZariskiDerived_eq (X : Scheme.{u}) :
    commSmallEtaleToZariskiDerived X =
      (IsFlat.exactPullback (commSmallEtaleToZariski X)).mapDerivedCategory :=
  sorry

end AlgebraicGeometry.Scheme.SiteRestriction
