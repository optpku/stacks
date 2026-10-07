module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.InternalHom

variable {X X' S S' : Scheme.{u}}
variable {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X'.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X'.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X'.toRingedSpace]
variable [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f'.toShHom)]
variable [IsIso
  (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
variable [IsIso
  (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]

/-- The scheme-level derived internal-Hom base-change morphism: first apply derived base change
to the internal Hom, then push forward the pullback/internal-Hom comparison. -/
noncomputable def map (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (M K : RingedSpace.ModuleDerived X.toRingedSpace) :
    (RingedSpace.Hom.DerivedBaseChange.source f.toShHom g.toShHom).obj
        ((H_X.ihomOf M).obj K) ⟶
      (RingedSpace.moduleDerivedPushforward f'.toShHom).obj
        ((H_X'.ihomOf
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj M)).obj
          ((RingedSpace.modulePullbackDerived g'.toShHom).obj K)) :=
  (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
    (RingedSpace.moduleDerivedPushforward f'.toShHom).map
      (Functor.PullbackInternalHom.comparisonOf H_X H_X'
        (RingedSpace.modulePullbackDerived g'.toShHom)
        (fun A B ↦ (Functor.Monoidal.μIso
          (RingedSpace.modulePullbackDerived g'.toShHom) A B).symm)
        M K)

/-- The scheme-level internal-Hom base-change morphism is the derived base-change component
followed by derived pushforward of the pullback/internal-Hom comparison. -/
theorem map_spec (sq : CommSq g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (M K : RingedSpace.ModuleDerived X.toRingedSpace) :
    map sq H_X H_X' M K =
      (DerivedBaseChange.map sq).app ((H_X.ihomOf M).obj K) ≫
        (RingedSpace.moduleDerivedPushforward f'.toShHom).map
          (Functor.PullbackInternalHom.comparisonOf H_X H_X'
            (RingedSpace.modulePullbackDerived g'.toShHom)
            (fun A B ↦ (Functor.Monoidal.μIso
              (RingedSpace.modulePullbackDerived g'.toShHom) A B).symm)
            M K) := sorry

end AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.InternalHom
