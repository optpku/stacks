module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.TensorPushforward

/-!
# Base change for internal Hom and derived pushforward

This module constructs the internal-Hom pushforward base-change morphism whose target uses
ordinary termwise pullback of the coefficient complex.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X' X S' S : Scheme.{u}}
variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [KFlat.HomotopyTensorDescends X'.toRingedSpace]
variable [KFlat.TensorDescends X'.toRingedSpace]
variable [KFlat.IsLocalization X'.toRingedSpace]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f'.toShHom)]
variable [IsIso
  (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
variable [IsIso
  (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
variable [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]

/-- The canonical internal-Hom base-change morphism whose target uses the ordinary termwise
pullback of the complex `G`. -/
noncomputable def internalHomPushforwardBaseChangeMap
    (sq : IsPullback g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ) :
    (RingedSpace.Hom.DerivedBaseChange.source f.toShHom g.toShHom).obj
        ((H_X.ihomOf E).obj (DerivedCategory.Q.obj G)) ⟶
      (RingedSpace.moduleDerivedPushforward f'.toShHom).obj
        ((H_X'.ihomOf
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj E)).obj
          (DerivedCategory.Q.obj
            (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj G))) :=
  Scheme.Hom.DerivedBaseChange.InternalHom.map
      sq.toCommSq H_X H_X' E (DerivedCategory.Q.obj G) ≫
    (RingedSpace.moduleDerivedPushforward f'.toShHom).map
      ((H_X'.ihomOf
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj E)).map
        (pullbackComplexComparison g' G))

/-- The internal-Hom pushforward base-change morphism is internal-Hom derived base change
followed by pushforward of covariance along the ordinary-complex pullback comparison. -/
theorem internalHomPushforwardBaseChangeMap_def
    (sq : IsPullback g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (G : CochainComplex X.Modules ℤ) :
    internalHomPushforwardBaseChangeMap g' f' f g sq H_X H_X' E G =
      Scheme.Hom.DerivedBaseChange.InternalHom.map
          sq.toCommSq H_X H_X' E (DerivedCategory.Q.obj G) ≫
        (RingedSpace.moduleDerivedPushforward f'.toShHom).map
          ((H_X'.ihomOf
            ((RingedSpace.modulePullbackDerived g'.toShHom).obj E)).map
            (pullbackComplexComparison g' G)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
