module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.BoundedBelow

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open DerivedCategory.TStructure
open CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [CompactSpace X] [QuasiSeparatedSpace X]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [HomotopyTensorDescends X.toRingedSpace]
variable [TensorDescends X.toRingedSpace]
variable [IsLocalization X.toRingedSpace]
variable [HomotopyTensorDescends Y.toRingedSpace]
variable [TensorDescends Y.toRingedSpace]
variable [IsLocalization Y.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
variable [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]

/-- If both derived internal-Hom objects have quasicoherent cohomology, then the
uncoherated sheafy trace map is an isomorphism. -/
theorem uncoheratedSheafyTraceMapIsIsoOfDerivedQCoh
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y)
    [h_source : derivedQuasiCoherentModuleProperty X
      ((ihom L.obj).obj (a.obj K).obj)]
    [h_target : derivedQuasiCoherentModuleProperty Y
      ((ihom ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).obj K.obj)] :
    IsIso (uncoheratedSheafyTraceMap f a adj L K) := sorry

/-- If `L` and its derived pushforward are perfect, then the uncoherated sheafy
trace map is an isomorphism. -/
theorem uncoheratedSheafyTraceMapIsIsoOfPerfect
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y)
    [hL : Fact (RingedSpace.ModuleDerived.IsPerfect L.obj)]
    [hRfL : Fact (RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj))] :
    IsIso (uncoheratedSheafyTraceMap f a adj L K) := sorry

/-- If `K` is bounded below and `L` and its derived pushforward are
pseudo-coherent, then the uncoherated sheafy trace map is an isomorphism. -/
theorem uncoheratedSheafyTraceMapIsIsoOfPseudoCoherent
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y)
    [hK : Fact ((t.plus : ObjectProperty
      (RingedSpace.ModuleDerived Y.toRingedSpace)) K.obj)]
    [hL : Fact (RingedSpace.ModuleDerived.IsPseudoCoherent L.obj)]
    [hRfL : Fact (RingedSpace.ModuleDerived.IsPseudoCoherent
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj))] :
    IsIso (uncoheratedSheafyTraceMap f a adj L K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
