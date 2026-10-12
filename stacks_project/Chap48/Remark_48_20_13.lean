/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.RightAdjoint.ProperFlat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace NormalizedDualizingComplex

/- Remark 48.20.13: for a flat proper morphism `f : X ⟶ Y` of schemes of finite
type over the Noetherian pair `(S, ωS)`, the normalized dualizing complex `ωX` is
isomorphic to `Lf^*ωY ⊗ᴸ ωX/Y`. Here the intermediate term is `a.obj ωY`, and
`ωX/Y` is `DerivedQCoh.relativeDualizingComplex f' a aAdjunction = a.obj 𝒪_Y`. -/
@[stacks 0B6W] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isIsomorphic_pullbackTensor :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y)
    [IsProper f.hom.left] [Flat f.hom.left],
    let X' : Scheme := X.obj.left
    let Y' : Scheme := Y.obj.left
    let f' : X' ⟶ Y' := f.hom.left
    ∀ [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived X'.toRingedSpace)]
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived Y'.toRingedSpace)]
      (HY : MonoidalClosed (RingedSpace.ModuleDerived Y'.toRingedSpace))
      [HomotopyTensorDescends X'.toRingedSpace]
      [TensorDescends X'.toRingedSpace]
      [IsLocalization X'.toRingedSpace]
      [HomotopyTensorDescends Y'.toRingedSpace]
      [TensorDescends Y'.toRingedSpace]
      [IsLocalization Y'.toRingedSpace]
      [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f'.toShHom)]
      (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
      (ωX : Scheme.DerivedQCoh X') (ωY : Scheme.DerivedQCoh Y')
      (hX : @RelativeTo _ _ _ X.obj.hom (Scheme.FiniteTypeOver.instFiniteType X)
        _ HS _ HX ωS hωS ωX.obj)
      (hY : @RelativeTo _ _ _ Y.obj.hom (Scheme.FiniteTypeOver.instFiniteType Y)
        _ HS _ HY ωS hωS ωY.obj)
      (a : Scheme.DerivedQCoh Y' ⥤ Scheme.DerivedQCoh X')
      (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f' ⊣ a),
      IsIsomorphic ωX
        (Scheme.DerivedQCoh.tensorObj ((Scheme.DerivedQCoh.pullback f').obj ωY)
          (Scheme.DerivedQCoh.relativeDualizingComplex f' a aAdjunction)))

end NormalizedDualizingComplex
end Hom
end Scheme
end AlgebraicGeometry
