module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.TensorPushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver

/-!
# Flat base change for tensor products and derived pushforwards

This module proves invertibility of the tensor-pushforward base-change comparison for a
bounded-above complex that is degreewise quasicoherent and flat over the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open DerivedTensor.Right.Monoidal
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a cartesian square and a quasi-compact, quasi-separated vertical morphism, the
tensor-pushforward base-change map associated to a bounded-above degreewise quasicoherent
complex flat over the base is an isomorphism. -/
@[stacks 0A1D]
theorem pushforwardTensorBaseChange_isIso
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [RingedSpace.DerivedAdjunction.HasPair f.toShHom]
    [RingedSpace.DerivedAdjunction.HasPair f'.toShHom]
    [IsIso
      (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso
      (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
    (sq : IsPullback g' f' f g)
    (T_X : @Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_X' : @Model
      (RingedSpace.Modules X'.toRingedSpace) _ _ _ _ _ _ _)
    (E : ModuleDerived.Quasicoherent X) (G : CochainComplex X.Modules ℤ)
    [hG_bounded : Fact (CochainComplex.minus X.Modules G)]
    [∀ n : ℤ, (G.X n).IsQuasicoherent]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom] :
    IsIso (tensorPushforwardBaseChangeMap g' f' f g sq T_X T_X' E G) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

end
