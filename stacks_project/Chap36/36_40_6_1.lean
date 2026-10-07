module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero.Comparison.Support

universe u

/- 36.40.6.1: define `K'` as the derived pushforward `R(V ⟶ X) _* K`; this object is
canonically isomorphic to the derived extension by zero `R(V ⟶ X) _! K`. -/
@[stacks 0GER] #check
  (AlgebraicGeometry.RingedSpace.OpenSubspace.ExtensionByZero.isIsomorphic_derivedExtensionByZero_pushforward_of_isSupportedOn :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}}
      (U : TopologicalSpace.Opens X.carrier)
      [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
        (CategoryTheory.forget₂ CommRingCat RingCat.{u})]
      {T : Set X},
      IsClosed T → T ⊆ U →
        ∀ F : AlgebraicGeometry.RingedSpace.moduleDerivedOnOpen X U,
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsSupportedOn F (Subtype.val ⁻¹' T) →
            CategoryTheory.IsIsomorphic
              ((AlgebraicGeometry.RingedSpace.moduleExtensionByZeroFromOpenDerived X U).obj F)
              ((AlgebraicGeometry.RingedSpace.modulePushforwardFromOpenDerived U).obj F))
