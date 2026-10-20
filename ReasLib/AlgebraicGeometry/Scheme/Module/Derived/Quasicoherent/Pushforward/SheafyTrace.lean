module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ProjectionFormula
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]

/-- The sheafy trace comparison before applying the quasicoherent coherator. -/
noncomputable def uncoheratedSheafyTraceMap
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    (RingedSpace.moduleDerivedPushforward f.toShHom).obj
        ((ihom L.obj).obj (a.obj K).obj) ⟶
      (ihom ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).obj K.obj :=
  @InternalHom.comparison _ _ _ _ _ _
      (RingedSpace.moduleDerivedPushforward f.toShHom)
      (@CategoryTheory.Adjunction.rightAdjointLaxMonoidal _ _ _ _ _ _ _ _
        (RingedSpace.modulePullbackDerivedPushforwardAdjunction f.toShHom)
        (Functor.Monoidal.toOplaxMonoidal
          (F := RingedSpace.modulePullbackDerived f.toShHom))) L.obj (a.obj K).obj _ _ ≫
    (ihom ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).map
      ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
        (inclusion Y).map (adj.counit.app K))

/-- The sheafy trace comparison after applying the quasicoherent coherator. -/
noncomputable def coheratedSheafyTraceMap
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    (inclusion Y).rightAdjoint.obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          ((ihom L.obj).obj (a.obj K).obj)) ⟶
      (inclusion Y).rightAdjoint.obj
        ((ihom ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).obj K.obj) :=
  (inclusion Y).rightAdjoint.map (uncoheratedSheafyTraceMap f a adj L K)

/-- The sheafy trace comparison is given by the internal-Hom comparison followed by the
included counit of the chosen derived pushforward adjunction. -/
theorem coheratedSheafyTraceMap_eq
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    coheratedSheafyTraceMap f a adj L K =
      (inclusion Y).rightAdjoint.map
        (@InternalHom.comparison _ _ _ _ _ _
          (RingedSpace.moduleDerivedPushforward f.toShHom)
          (@CategoryTheory.Adjunction.rightAdjointLaxMonoidal _ _ _ _ _ _ _ _
            (RingedSpace.modulePullbackDerivedPushforwardAdjunction f.toShHom)
            (Functor.Monoidal.toOplaxMonoidal
              (F := RingedSpace.modulePullbackDerived f.toShHom))) L.obj (a.obj K).obj _ _ ≫
          (ihom ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).map
            ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
              (inclusion Y).map (adj.counit.app K))) := sorry

/-- Applying the quasicoherent coherator to the uncoherated sheafy trace comparison
gives the coherated sheafy trace comparison. -/
theorem coheratedSheafyTraceMap_eq_mapUncoherated
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    coheratedSheafyTraceMap f a adj L K =
      (inclusion Y).rightAdjoint.map (uncoheratedSheafyTraceMap f a adj L K) := sorry

/-- The coherated sheafy trace comparison is invertible for quasicoherent derived modules. -/
instance coheratedSheafyTraceMapIsIso
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    IsIso (coheratedSheafyTraceMap f a adj L K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
