module

public import ReasLib.AlgebraicGeometry.BivariantClass.ZeroScheme

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.BivariantClass.gysin :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (s : L.sections),
    AlgebraicGeometry.BivariantClass δ
      (Over.homMk (AlgebraicGeometry.Scheme.zeroSchemeι L s) :
        Over.mk (AlgebraicGeometry.Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X) 1)
