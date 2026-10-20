module

public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction
public import Mathlib.Algebra.Group.Center

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology

/-- Restricting a first Chern class gives the first Chern class of the pulled-back
invertible module. -/
theorem restrictDegree_firstChernClass
    {S X X' : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (f : X' ⟶ X) [LocallyOfFiniteType f]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    restrictDegree δ (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) 1
        (firstChernClass δ p ℒ) =
      firstChernClass δ (f ≫ p) ((Scheme.Modules.pullback f).obj ℒ) := sorry

/-- Composition with a first Chern class commutes with moving the class across a
locally finite-type morphism, after pulling back the invertible module. -/
theorem comp_firstChernClass
    {S X X' : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (f : X' ⟶ X) [LocallyOfFiniteType f]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (q : ℤ)
    (c : BivariantClass δ (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) q) :
    HEq
      (BivariantClass.comp δ (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)
        (𝟙 (Over.mk p)) c (firstChernClass δ p ℒ))
      (BivariantClass.comp δ (𝟙 (Over.mk (f ≫ p)))
        (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)
        (firstChernClass δ (f ≫ p) ((Scheme.Modules.pullback f).obj ℒ)) c) := sorry

/-- The degree-one first Chern class of an invertible module is central in the full
Chow cohomology ring. -/
theorem firstChernClass_mem_center
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    DirectSum.of (degree δ p) (1 : ℤ) (firstChernClass δ p ℒ) ∈
      Set.center (ring δ p) := sorry

end AlgebraicGeometry.ChowCohomology
