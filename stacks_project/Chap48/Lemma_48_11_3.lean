/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Coextension
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat

/- Lemma 48.11.3: for an affine morphism `f : Y ⟶ X`, derived coextension along
`𝒪_X ⟶ f_*𝒪_Y`, followed by derived restriction of scalars, is naturally isomorphic to
derived internal Hom from `f_*𝒪_Y` in `D(𝒪_X)`. -/
@[stacks 0BV1]
#check (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.derivedRestrictionCoextension_isomorphic_internalHom :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)),
    IsIsomorphic
      (SheafOfModules.RingedSite.DerivedCoextension.functor.{u, u}
          (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) ⋙
        SheafOfModules.RingedSite.DerivedCoextension.restriction.{u, u}
          (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))
      (MonoidalClosed.ihomOf H
        ((DerivedCategory.singleFunctor.{u + 1, u, u + 1} X.Modules 0).obj
          ((RingedSpace.Hom.pushforward f.toShHom).obj
            (SheafOfModules.unit Y.toRingedSpace.ringCatSheaf)))))
