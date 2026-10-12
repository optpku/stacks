/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern.Commutation

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DirectSum

universe u

#check (AlgebraicGeometry.ChowCohomology.restrictDegree_firstChernClass :
  ∀ {S X X' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p]
    (f : X' ⟶ X) [LocallyOfFiniteType f]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ],
    AlgebraicGeometry.ChowCohomology.restrictDegree δ
        (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) 1
        (AlgebraicGeometry.ChowCohomology.firstChernClass δ p ℒ) =
      AlgebraicGeometry.ChowCohomology.firstChernClass δ (f ≫ p)
        ((Scheme.Modules.pullback f).obj ℒ))

#check (AlgebraicGeometry.ChowCohomology.comp_firstChernClass :
  ∀ {S X X' : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p]
    (f : X' ⟶ X) [LocallyOfFiniteType f]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (q : ℤ)
    (c : AlgebraicGeometry.BivariantClass δ
      (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p) q),
    HEq
      (AlgebraicGeometry.BivariantClass.comp δ
        (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)
        (𝟙 (Over.mk p)) c
        (AlgebraicGeometry.ChowCohomology.firstChernClass δ p ℒ))
      (AlgebraicGeometry.BivariantClass.comp δ
        (𝟙 (Over.mk (f ≫ p)))
        (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)
        (AlgebraicGeometry.ChowCohomology.firstChernClass δ (f ≫ p)
          ((Scheme.Modules.pullback f).obj ℒ)) c))

#check (AlgebraicGeometry.ChowCohomology.firstChernClass_mem_center :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ],
    DirectSum.of (AlgebraicGeometry.ChowCohomology.degree δ p) (1 : ℤ)
        (AlgebraicGeometry.ChowCohomology.firstChernClass δ p ℒ) ∈
      Set.center (AlgebraicGeometry.ChowCohomology.ring δ p))
