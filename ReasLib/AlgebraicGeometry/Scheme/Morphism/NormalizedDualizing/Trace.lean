module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalClosed
open LocallyRingedSpace.Hom
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction
open Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {S : Scheme.{u}} [hS : IsNoetherian S]
variable {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y) [hProper : IsProper f.hom.left]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
  [HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
variable [homotopyTensorX : HomotopyTensorDescends
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
  [tensorX : TensorDescends
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
  [localizationX : IsLocalization
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left))]
variable [homotopyTensorY : HomotopyTensorDescends
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
  [tensorY : TensorDescends
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
  [localizationY : IsLocalization
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left))]
variable [HX : MonoidalClosed (RingedSpace.ModuleDerived
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X.obj.left)))]
  [HY : MonoidalClosed (RingedSpace.ModuleDerived
    (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace Y.obj.left)))]
variable (ωS : RingedSpace.ModuleDerived S.toRingedSpace)
  (hωS : ωS.IsDualizingComplex HS)
variable (ωX : DerivedQCoh X.obj.left) (ωY : DerivedQCoh Y.obj.left)

/-- The canonical comparison identifies the right adjoint of proper pushforward on the target
with the normalized dualizing complex on the source. -/
noncomputable def normalizedDualizingRightAdjointIso
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj) :
    (pushforwardCohomologyIn f.hom.left).rightAdjoint.obj ωY ≅ ωX := by
  let a := (pushforwardCohomologyIn f.hom.left).rightAdjoint
  let adj := Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f.hom.left)
  exact Classical.choice
    (Hom.NormalizedDualizingComplex.RelativeTo.isIsomorphic_rightAdjoint_of_isProper
      f HS HX HY ωS hωS ωX ωY hX hY a adj)

/-- The trace of a proper morphism on normalized dualizing complexes is the counit of the
canonical pushforward right adjunction transported across the normalized comparison. -/
noncomputable def normalizedDualizingTrace
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj) :
    (pushforwardCohomologyIn f.hom.left).obj ωX ⟶ ωY := by
  let a := (pushforwardCohomologyIn f.hom.left).rightAdjoint
  let adj := Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f.hom.left)
  let e := normalizedDualizingRightAdjointIso f ωS hωS ωX ωY hX hY
  exact (pushforwardCohomologyIn f.hom.left).map e.inv ≫ adj.counit.app ωY

/-- The normalized trace is the counit transported along the canonical comparison. -/
theorem normalizedDualizingTrace_eq
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj) :
    normalizedDualizingTrace f ωS hωS ωX ωY hX hY =
      (pushforwardCohomologyIn f.hom.left).map
          (normalizedDualizingRightAdjointIso f ωS hωS ωX ωY hX hY).inv ≫
        (Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f.hom.left)).counit.app ωY := sorry

/-- The normalized dualizing Hom equivalence identifies maps into the source dualizing complex
with maps from their proper pushforward into the target dualizing complex. -/
noncomputable def normalizedDualizingHomEquiv
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj)
    (L : DerivedQCoh X.obj.left) :
    (L ⟶ ωX) ≃ ((pushforwardCohomologyIn f.hom.left).obj L ⟶ ωY) := by
  let a := (pushforwardCohomologyIn f.hom.left).rightAdjoint
  let adj := Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f.hom.left)
  let e := normalizedDualizingRightAdjointIso f ωS hωS ωX ωY hX hY
  exact ((Iso.refl L).homCongr e.symm).trans (adj.homEquiv L ωY).symm

/-- The normalized dualizing Hom equivalence sends a morphism to its pushforward followed by
the normalized dualizing trace. -/
theorem normalizedDualizingHomEquiv_apply
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj)
    (L : DerivedQCoh X.obj.left) (g : L ⟶ ωX) :
    normalizedDualizingHomEquiv f ωS hωS ωX ωY hX hY L g =
      (pushforwardCohomologyIn f.hom.left).map g ≫
        normalizedDualizingTrace f ωS hωS ωX ωY hX hY := sorry

variable
  [derivedAdjunction : HasPair
    (RingedSpace.opensRingedSiteHom (toShHom (toLRSHom f.hom.left)))]
  [pullbackMonoidal : Functor.Monoidal
    (RingedSpace.modulePullbackDerived (toShHom (toLRSHom f.hom.left)))]

/-- The sheafy normalized dualizing trace comparison is obtained by transporting the source
internal Hom along the canonical normalized comparison and applying the sheafy trace. -/
noncomputable def normalizedDualizingSheafyTraceMap
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj)
    (L : DerivedQCoh X.obj.left) :
    (RingedSpace.moduleDerivedPushforward (toShHom (toLRSHom f.hom.left))).obj
        ((ihom L.obj).obj ωX.obj) ⟶
      (ihom ((RingedSpace.moduleDerivedPushforward (toShHom (toLRSHom f.hom.left))).obj
        L.obj)).obj ωY.obj := by
  let a := (pushforwardCohomologyIn f.hom.left).rightAdjoint
  let adj := Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f.hom.left)
  let e := normalizedDualizingRightAdjointIso f ωS hωS ωX ωY hX hY
  exact
    (RingedSpace.moduleDerivedPushforward (toShHom (toLRSHom f.hom.left))).map
        ((ihom L.obj).map ((inclusion X.obj.left).map e.inv)) ≫
      @uncoheratedSheafyTraceMap X.obj.left Y.obj.left f.hom.left
        inferInstance inferInstance inferInstance
        homotopyTensorX tensorX localizationX homotopyTensorY tensorY localizationY
        HX HY derivedAdjunction pullbackMonoidal a adj L ωY

/-- The sheafy normalized dualizing trace comparison is transport followed by the canonical
uncoherated sheafy trace map. -/
theorem normalizedDualizingSheafyTraceMap_eq
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj)
    (L : DerivedQCoh X.obj.left) :
    normalizedDualizingSheafyTraceMap f ωS hωS ωX ωY hX hY L =
      (RingedSpace.moduleDerivedPushforward (toShHom (toLRSHom f.hom.left))).map
          ((ihom L.obj).map ((inclusion X.obj.left).map
            (normalizedDualizingRightAdjointIso f ωS hωS ωX ωY hX hY).inv)) ≫
        @uncoheratedSheafyTraceMap X.obj.left Y.obj.left f.hom.left
          inferInstance inferInstance inferInstance
          homotopyTensorX tensorX localizationX homotopyTensorY tensorY localizationY
          HX HY derivedAdjunction pullbackMonoidal
          (pushforwardCohomologyIn f.hom.left).rightAdjoint
          (Adjunction.ofIsLeftAdjoint (pushforwardCohomologyIn f.hom.left)) L ωY := sorry

/-- The normalized dualizing sheafy trace comparison is invertible. -/
theorem normalizedDualizingSheafyTraceMapIsIso
    (hX : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ X.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX.obj)
    (hY : @Hom.NormalizedDualizingComplex.RelativeTo _ _ _ Y.obj.hom
      (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY.obj)
    (L : DerivedQCoh X.obj.left) :
    IsIso (normalizedDualizingSheafyTraceMap f ωS hωS ωX ωY hX hY L) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
