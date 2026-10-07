module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Extension
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- 91.4.0.1: along a first-order thickening i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'}) of ringed
spaces, the displayed sequence 0 ⟶ 𝒦 ⟶ ℱ' ⟶ ℱ ⟶ 0 of 𝒪_{X'}-modules with
𝒦, ℱ : X.Modules and middle term ℱ' is ModuleExtension.toShortComplex, i.e.
0 ⟶ i _* 𝒦 ⟶ ℱ' ⟶ i _* ℱ ⟶ 0. -/
@[stacks 08L4] #check
  (AlgebraicGeometry.RingedSpace.Hom.ModuleExtension.toShortComplex :
    ∀ {X X' : AlgebraicGeometry.RingedSpace.{u}} {i : X ⟶ X'},
      AlgebraicGeometry.RingedSpace.Hom.ModuleExtension i →
        CategoryTheory.ShortComplex X'.Modules)
#check
  (AlgebraicGeometry.RingedSpace.Hom.ModuleExtension.shortExact :
    ∀ {X X' : AlgebraicGeometry.RingedSpace.{u}} {i : X ⟶ X'}
      (E : AlgebraicGeometry.RingedSpace.Hom.ModuleExtension i),
      (E.toShortComplex).ShortExact)
