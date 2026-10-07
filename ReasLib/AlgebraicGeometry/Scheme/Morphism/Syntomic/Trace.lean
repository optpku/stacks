module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Dualizable
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat
public import ReasLib.LinearAlgebra.Trace.Projective

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The commutative-algebra multiplication on the pushed-forward structure module. -/
noncomputable def pushforwardStructureMul
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    f.pushforwardStructureModule ⊗ f.pushforwardStructureModule ⟶
      f.pushforwardStructureModule :=
  -- Local instance justification (defeq pin): fixes the pullback structure used to derive the matching lax structure.
  letI : (Scheme.Modules.pullback f).Monoidal :=
    Scheme.Modules.pullbackMonoidal f
  -- Local instance justification (defeq pin): fixes the adjunction-derived lax structure used by `mapMon`.
  letI : (Scheme.Modules.pushforward f).LaxMonoidal :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjointLaxMonoidal
  let A := (Scheme.Modules.pushforward f).mapMon.obj (Mon.trivial Y.Modules)
  let e : A.X ≅ f.pushforwardStructureModule :=
    (Scheme.Modules.pushforward f).mapIso
      (RingedSpace.unitIsoTensorUnit Y.toRingedSpace).symm
  @MonObj.mul X.Modules _ _ f.pushforwardStructureModule (MonObj.ofIso e)

/-- Multiplication on the pushed-forward structure module is associative. -/
theorem pushforwardStructureMul_assoc
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pushforwardStructureMul f ▷ f.pushforwardStructureModule) ≫
        pushforwardStructureMul f =
      (α_ f.pushforwardStructureModule f.pushforwardStructureModule
        f.pushforwardStructureModule).hom ≫
        (f.pushforwardStructureModule ◁ pushforwardStructureMul f) ≫
        pushforwardStructureMul f := sorry

/-- Pullback of a structure module followed by its canonical comparison with the structure
module on the source. -/
noncomputable def pullbackStructureModuleMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj
        (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (Scheme.Modules.pullback f).map
      (RingedSpace.unitIsoTensorUnit Y.toRingedSpace).hom ≫
    (Scheme.Modules.pullbackUnitIso f).hom ≫
    RingedSpace.tensorUnitToUnitModule X.toRingedSpace

/-- The canonical pullback comparison for structure modules is an isomorphism. -/
theorem pullbackStructureModuleMap_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (pullbackStructureModuleMap f) := sorry

/-- The trace of multiplication on the finite locally free algebra `f_*𝒪f_Y`. -/
noncomputable def finiteSyntomicTrace
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Syntomic f] :
    f.pushforwardStructureModule ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  -- Local instance justification (proof-local temporary data): finite syntomicity supplies finite local freeness only for dualizability.
  letI : IsFiniteLocallyFree f :=
    isFiniteLocallyFree_of_isFinite_and_flat_and_locallyOfFinitePresentation
      inferInstance inferInstance inferInstance
  -- Local instance justification (proof-local temporary data): dualizability supplies this inverse only for the internal trace construction.
  letI : IsIso
      (MonoidalClosed.tensorIhomUnitToEnd f.pushforwardStructureModule) :=
    (SheafOfModules.IsFiniteLocallyFree.isRightDualizable
      f.pushforwardStructureModule).isIso_tensorIhomUnitToEnd
  curry (pushforwardStructureMul f) ≫
    MonoidalClosed.tensorIhomUnitToEndInv f.pushforwardStructureModule ≫
    (β_ f.pushforwardStructureModule
      (MonoidalClosed.dual f.pushforwardStructureModule)).hom ≫
    MonoidalClosed.Dual.evaluation f.pushforwardStructureModule ≫
    RingedSpace.tensorUnitToUnitModule X.toRingedSpace

/-- On affine schemes, `finiteSyntomicTrace` is the sheaf map induced by
`Algebra.FiniteProjective.trace` on global sections. -/
theorem finiteSyntomicTrace_affine
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] [IsAffine Y]
    [IsFinite f] [Syntomic f]
    [Algebra Γ(X, ⊤) Γ(Y, ⊤)] [Module.Finite Γ(X, ⊤) Γ(Y, ⊤)]
    [Module.Projective Γ(X, ⊤) Γ(Y, ⊤)]
    (h_algebra : algebraMap Γ(X, ⊤) Γ(Y, ⊤) = (f.app ⊤).hom) :
    ∀ s : Γ(Y, ⊤),
      Scheme.Modules.Hom.app (finiteSyntomicTrace f) ⊤ s =
        Algebra.FiniteProjective.trace Γ(X, ⊤) Γ(Y, ⊤) s := sorry

/-- The structure-sheaf trace commutes with every cartesian base change. -/
theorem finiteSyntomicTrace_baseChange
    {X' X Y' Y : Scheme.{u}}
    (b : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (a : X' ⟶ X)
    (sq : IsPullback b f' f a) [IsFinite f] [Syntomic f]
    [IsFinite f'] [Syntomic f'] :
    (Scheme.Modules.fromRingedSpace X').map
        ((RingedSpace.Hom.BaseChange.map
          (sq.toCommSq.map
            (Scheme.forgetToLocallyRingedSpace ⋙
              LocallyRingedSpace.forgetToSheafedSpace))).app
            (SheafOfModules.unit Y.ringCatSheaf)) ≫
        (Scheme.Modules.pushforward f').map
          (pullbackStructureModuleMap b) ≫
        finiteSyntomicTrace f' =
      (Scheme.Modules.pullback a).map (finiteSyntomicTrace f) ≫
        pullbackStructureModuleMap a := sorry

end AlgebraicGeometry.Scheme.Hom
