/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor

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

/-- For a morphism of finite presentation and a pseudo-coherent derived module, the derived
pushforward of its tensor product with a bounded-above complex of finitely presented modules
that is flat with proper support over the base is pseudo-coherent. -/
theorem pushforward_tensor_isPseudoCoherent_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E)
    (G : CochainComplex X.Modules ℤ)
    (hG_boundedAbove : CochainComplex.minus X.Modules G)
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f (G.X n)] :
    RingedSpace.ModuleDerived.IsPseudoCoherent
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        (DerivedTensor.Right.obj E (DerivedCategory.Q.obj G))) := sorry

/-- For a morphism of finite presentation and a pseudo-coherent derived module, the
tensor-pushforward base-change comparison associated to a bounded-above complex of finitely
presented modules that is flat with proper support over the base is an isomorphism for every
cartesian square. -/
theorem pushforward_tensor_baseChange_isIso_of_pseudoCoherent
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E)
    (G : CochainComplex X.Modules ℤ)
    (hG_boundedAbove : CochainComplex.minus X.Modules G)
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
      g' f' f g sq T_X T_X'
        ⟨E, PseudoCoherent.derivedQuasiCoherentModuleProperty hE⟩ G) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
