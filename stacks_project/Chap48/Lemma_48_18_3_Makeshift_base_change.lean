/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.MakeshiftBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory.Plus.CohomologyIn
open RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of

/- Lemma 48.18.3 (Makeshift base change): in a cartesian square of finite-type
separated schemes over a Noetherian base, if the right vertical map is flat and
the pullback of `E` has a bounded-below representative, then the two upper-shriek
base-change objects become isomorphic after restriction to any affine open mapping
into affine opens on the other three schemes. -/
@[stacks 0BZY] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.upperShriek_makeshiftBaseChange_isomorphic :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X' X Y' Y : FiniteTypeSeparatedOver S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (sq : IsPullback g'.hom.left f'.hom.left f.hom.left g.hom.left)
      [Flat f.hom.left]
      (P : Of Y.obj.left (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint P.obj.right.hom)
      (P' : Of Y'.obj.left (Over.mk f'.hom.left))
      (A' : DerivedQCoh.PlusRightAdjoint P'.obj.right.hom)
      (E : DerivedQCoh.Plus Y.obj.left) (Eg : DerivedQCoh.Plus Y'.obj.left)
      (hEg : IsIsomorphic
        ((toUnbounded (quasiCoherentModuleProperty (Over.left Y'.obj))).obj Eg)
        ((DerivedQCoh.pullback g.hom.left).obj
          ((toUnbounded (quasiCoherentModuleProperty (Over.left Y.obj))).obj E)))
      (U' : (Over.left X'.obj).affineOpens) (U : (Over.left X.obj).affineOpens)
      (V' : (Over.left Y'.obj).affineOpens) (V : (Over.left Y.obj).affineOpens)
      (hU : U' ≤ g'.hom.left ⁻¹ᵁ U) (hV' : U' ≤ f'.hom.left ⁻¹ᵁ V')
      (hV : U' ≤ (g' ≫ f).hom.left ⁻¹ᵁ V),
      IsIsomorphic
        ((upperShriek f P A.plus ⋙
          toUnbounded (quasiCoherentModuleProperty (Over.left X.obj)) ⋙
          DerivedQCoh.pullback g'.hom.left ⋙
          DerivedQCoh.OpenImmersion.pullback U'.1.ι ⋙
          DerivedQCoh.inclusion U'.1.toScheme).obj E)
        ((upperShriek f' P' A'.plus ⋙
          toUnbounded (quasiCoherentModuleProperty (Over.left X'.obj)) ⋙
          DerivedQCoh.OpenImmersion.pullback U'.1.ι ⋙
          DerivedQCoh.inclusion U'.1.toScheme).obj Eg))

end Of
end Compactification
end Scheme
end AlgebraicGeometry
