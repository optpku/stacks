/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.InternalHomPushforward.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.Scheme.DerivedQCoh
open RingedSite.Hom.DerivedAdjunction
open scoped CartesianClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- For a locally finite type morphism to a Noetherian scheme, the derived pushforward of
the internal Hom from a perfect object to a bounded, termwise coherent and relatively flat
complex having cohomologically proper support over the base is perfect. -/
theorem pushforward_internalHom_isPerfect
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (G : CochainComplex X.Modules ℤ)
    (hG_bounded : CochainComplex.bounded X.Modules G)
    [∀ i : ℤ, (G.X i).IsCoherent]
    [∀ i : ℤ, SheafOfModules.IsFlatOver (G.X i) f.toShHom]
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
      (RingedSpace.ModuleDerived.cohomologySheaf (DerivedCategory.Q.obj G) i)] :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        (E ⟹ DerivedCategory.Q.obj G)) := sorry

/-- If `f : X ⟶ S` is of finite presentation, `E` is perfect, and `G` is a bounded
complex whose terms are finitely presented, flat over `S`, and have proper support over `S`,
then the derived pushforward of the internal Hom from `E` to `Q.obj G` is perfect. -/
theorem pushforward_internalHom_isPerfect_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (G : CochainComplex X.Modules ℤ)
    (hG_bounded : CochainComplex.bounded X.Modules G)
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f (G.X n)] :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        (E ⟹ DerivedCategory.Q.obj G)) := sorry

/-- Under the finite-presentation, perfectness, boundedness, flatness, and proper-support
hypotheses, the canonical comparison for the derived pushforward of an internal Hom is an
isomorphism after every cartesian base change. -/
theorem pushforward_internalHom_baseChange_isIso_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (G : CochainComplex X.Modules ℤ)
    (hG_bounded : CochainComplex.bounded X.Modules G)
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f (G.X n)]
    {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S)
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace)) :
    IsIso (internalHomPushforwardBaseChangeMap
      g' f' f g sq H_X H_X' E G) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
