module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero.Comparison.Support

open CategoryTheory TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

universe u

/- 36.40.5.1: define `K'` as the derived pushforward `R(V → X) _* K`; because `K`
is supported on the closed subset `X \\ U` contained in `V`, this object is canonically
isomorphic to the derived extension by zero `R(V → X) _! K`. -/
@[stacks 0GEP] #check
  (AlgebraicGeometry.RingedSpace.OpenSubspace.ExtensionByZero.isIsomorphic_derivedExtensionByZero_pushforward_of_isSupportedOn :
  ∀ {X : RingedSpace.{u}} (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    {T : Set X} (hT_closed : IsClosed T) (hTU : T ⊆ U)
    (F : moduleDerivedOnOpen X U)
    (hF : ModuleDerived.IsSupportedOn F (Subtype.val ⁻¹' T)),
    CategoryTheory.IsIsomorphic ((moduleExtensionByZeroFromOpenDerived X U).obj F)
      ((modulePushforwardFromOpenDerived U).obj F))
