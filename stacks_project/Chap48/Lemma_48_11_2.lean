/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap48.Lemma_48_11_1
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Coextension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]

/- Lemma 48.11.2: for an affine morphism `f : Y ⟶ X`, total right-derived
coextension along `𝒪_X ⟶ f_*𝒪_Y` is right adjoint to derived restriction of scalars. -/
@[stacks 0BV0] #check
  (SheafOfModules.RingedSite.DerivedCoextension.adjunction
      (J := Opens.grothendieckTopology X.toTopCat)
      (𝒪 := X.sheaf)
      (𝒪' := (TopCat.Sheaf.pushforward CommRingCat f.toShHom.hom.base).obj Y.sheaf)
      (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) :
    SheafOfModules.RingedSite.DerivedCoextension.restriction
        (J := Opens.grothendieckTopology X.toTopCat)
        (𝒪 := X.sheaf)
        (𝒪' := (TopCat.Sheaf.pushforward CommRingCat f.toShHom.hom.base).obj Y.sheaf)
        (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) ⊣
      SheafOfModules.RingedSite.DerivedCoextension.functor
        (J := Opens.grothendieckTopology X.toTopCat)
        (𝒪 := X.sheaf)
        (𝒪' := (TopCat.Sheaf.pushforward CommRingCat f.toShHom.hom.base).obj Y.sheaf)
        (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))

end Scheme
end AlgebraicGeometry
