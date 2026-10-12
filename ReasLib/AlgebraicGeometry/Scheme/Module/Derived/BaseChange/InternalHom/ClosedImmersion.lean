/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ClosedImmersion.InternalHom
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison

@[expose] public section

/-!
# Internal-Hom base change for closed immersions

This module relates right-adjoint base change for a closed immersion to the corresponding
pullback/internal-Hom comparison.
-/

open AlgebraicGeometry CategoryTheory RingedSite.Hom RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TorIndependentBaseChange

/-- In a Tor-independent cartesian square with `i : Z ⟶ X` a closed immersion, the
right-adjoint base-change component is invertible exactly when the pullback/internal-Hom
comparison from `L(f)^* Rℋom(𝒪_Z, K)` is invertible. -/
theorem rightAdjoint_isIso_iff_internalHom
    {Z' Z X' X : Scheme.{u}}
    (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (f : X' ⟶ X)
    [DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom i.toShHom)]
    [DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom i'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      i'.toShHom f.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison
      g.toShHom i.toShHom)]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [(RingedSpace.modulePullbackDerived f.toShHom).Monoidal]
    (sq : IsPullback g i' i f) [IsClosedImmersion i]
    (hTor : Scheme.TorIndependentOver (Over.mk i) (Over.mk f))
    (rHomOZ : RingedSpace.ModuleDerived X.toRingedSpace ⥤
      RingedSpace.ModuleDerived Z.toRingedSpace)
    (rHomOZPrime : RingedSpace.ModuleDerived X'.toRingedSpace ⥤
      RingedSpace.ModuleDerived Z'.toRingedSpace)
    (iAdj : RingedSpace.moduleDerivedPushforward i.toShHom ⊣ rHomOZ)
    (iPrimeAdj : RingedSpace.moduleDerivedPushforward i'.toShHom ⊣ rHomOZPrime)
    (baseChangeIso :
      RingedSpace.modulePullbackDerived g.toShHom ⋙
          RingedSpace.moduleDerivedPushforward i'.toShHom ≅
        RingedSpace.moduleDerivedPushforward i.toShHom ⋙
          RingedSpace.modulePullbackDerived f.toShHom)
    (h_baseChange : baseChangeIso.inv =
      Hom.DerivedBaseChange.map sq.toCommSq)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsIso (CategoryTheory.DerivedBaseChange.app iAdj iPrimeAdj baseChangeIso K) ↔
      IsIso (Functor.PullbackInternalHom.comparisonOf H_X H_X'
        (RingedSpace.modulePullbackDerived f.toShHom)
        (fun A B ↦ (Functor.Monoidal.μIso
          (RingedSpace.modulePullbackDerived f.toShHom) A B).symm)
        ((DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).obj
          ((RingedSpace.Hom.pushforward i.toShHom).obj
            (SheafOfModules.unit Z.toRingedSpace.ringCatSheaf))) K) := sorry

end AlgebraicGeometry.Scheme.TorIndependentBaseChange
