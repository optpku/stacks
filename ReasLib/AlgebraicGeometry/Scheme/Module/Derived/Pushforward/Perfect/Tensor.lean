module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.TensorPushforward.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived
open DerivedTensor.Right.Monoidal
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- For a locally finite type morphism to a Noetherian scheme, the derived pushforward of
the tensor product of a perfect object with a bounded, termwise coherent and relatively flat
complex having cohomologically proper support over the base is perfect. -/
theorem pushforward_tensor_isPerfect
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]
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
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))) := sorry

/-- For a morphism of finite presentation and a perfect derived module, the tensor-pushforward
base-change comparison associated to a bounded complex of finitely presented modules that is
flat with proper support over the base is an isomorphism for every cartesian square. -/
theorem pushforward_tensor_baseChange_isIso_of_finitePresentation
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
    (T_X : @Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_X' : @Model
      (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _) :
    IsIso (Scheme.DerivedQCoh.tensorPushforwardBaseChangeMap
      g' f' f g sq T_X T_X' ((PerfectDerived.toDerivedQCoh X).obj ⟨E, hE⟩) G) := sorry

/-- For a morphism of finite presentation, the derived pushforward of the tensor product of a
perfect object with a bounded complex of finitely presented modules that is flat with proper
support over the base is perfect. -/
theorem pushforward_tensor_isPerfect_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (G : CochainComplex X.Modules ℤ)
    (hG_bounded : CochainComplex.bounded X.Modules G)
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f (G.X n)] :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
