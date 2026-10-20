module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SelfFibreProduct
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory CategoryTheory.TwoFibreProduct

universe u

namespace AlgebraicGeometry.Groupoids

/- 100.3.6.1: The canonical self-fibre-product comparison is compatible with base change. -/
@[stacks 04Y7] #check (AlgebraicGeometry.Groupoids.selfComparison_whisker_eq :
  ∀ {S : Scheme.{u}} {U X X' : GroupoidsOver S} (f : U ⟶ X) (g : X' ⟶ X),
    let psi := selfFibreCospan f g
    let f' := TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g
    TwoFibreProduct.map.comparisonIso psi =
      whiskerRightIso (TwoFibreProduct.map.fstIso psi) f ≪≫
        α_ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') psi.left f ≪≫
        whiskerLeftIso (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') psi.leftIso ≪≫
        (α_ (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f' f') f' psi.base).symm ≪≫
        whiskerRightIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} f' f')
          psi.base ≪≫
        α_ (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f') f' psi.base ≪≫
        whiskerLeftIso (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f')
          psi.rightIso.symm ≪≫
        (α_ (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f' f') psi.right f).symm ≪≫
        whiskerRightIso (TwoFibreProduct.map.sndIso psi).symm f)

end AlgebraicGeometry.Groupoids
