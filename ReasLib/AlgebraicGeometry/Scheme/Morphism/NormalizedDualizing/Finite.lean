module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Trace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine.BoundedBelow
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.TraceComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite morphisms and relatively normalized dualizing complexes

This module identifies the affine pushforward of a relatively normalized dualizing complex
along a finite morphism with derived internal Hom, and compares the normalized trace with
evaluation at one.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open DerivedCategory.Plus
open CohomologyIn
open SheafOfModules.RingedSite
open LocallyRingedSpace.Hom
open RingedSpace.ModuleDerived.KFlat
open Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a finite morphism of schemes of finite type over a Noetherian base, affine pushforward
of a dualizing complex normalized relative to the base is isomorphic, in the bounded-below
derived category of quasicoherent modules over the pushed-forward structure sheaf, to derived
internal Hom from that structure sheaf into the normalized dualizing complex on the target. -/
theorem normalizedDualizing_affinePushforward_isIsomorphic_internalHom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [IsFinite f.hom.left]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived X.obj.left.toRingedSpace)]
    (HX : MonoidalClosed (RingedSpace.ModuleDerived X.obj.left.toRingedSpace))
    [MonoidalCategory (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace)]
    (HY : MonoidalClosed (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace))
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
    (ωX : DerivedQCoh.Plus X.obj.left) (ωY : DerivedQCoh.Plus Y.obj.left)
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj.obj) :
    IsIsomorphic
      ((affinePushforwardToPushforwardStructurePlus f.hom.left).obj ωX)
      ((derivedInternalHomPlus f.hom.left).obj ωY) := sorry

/-- Along a finite morphism of schemes of finite type over a Noetherian base, the normalized
trace of relatively normalized dualizing complexes agrees with evaluation at one after the
identification of affine pushforward with derived internal Hom. -/
theorem normalizedDualizingTrace_eq_evaluationAtOne
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [IsFinite f.hom.left]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    [HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
    [HomotopyTensorDescends
      (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
    [TensorDescends
      (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
    [IsLocalization
      (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
    [HomotopyTensorDescends
      (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
    [TensorDescends
      (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
    [IsLocalization
      (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
    [HX : MonoidalClosed (RingedSpace.ModuleDerived
      (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left)))]
    [HY : MonoidalClosed (RingedSpace.ModuleDerived
      (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left)))]
    (ωS : RingedSpace.ModuleDerived S.toRingedSpace)
    (hωS : ωS.IsDualizingComplex HS)
    (ωX : DerivedQCoh.Plus X.obj.left) (ωY : DerivedQCoh.Plus Y.obj.left)
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj.obj) :
    ∃ (e :
      ((DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace)).ι).obj
        ((pushforwardCohomologyIn f.hom.left).obj
          ((toUnbounded
              (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace)).obj ωX)) ≅
      (DerivedCoextension.restriction
          (RingedSpace.Hom.commRingSheafPushforwardMap f.hom.left.toShHom)).obj
        ((DerivedCoextension.functor
            (RingedSpace.Hom.commRingSheafPushforwardMap f.hom.left.toShHom)).obj
          ((ambient
            (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace)).obj ωY))),
      e.hom ≫ structureSheafInducedMap f.hom.left ωY =
        ((DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace)).ι).map
          (normalizedDualizingTrace f ωS hωS
            ((toUnbounded
                (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace)).obj ωX)
            ((toUnbounded
                (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace)).obj ωY)
            hX hY) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
