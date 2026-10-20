module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.CohomologicalDimension

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
variable [IsNoetherian X] [IsNoetherian Y] [IsProper f]
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

/-- For a proper morphism of Noetherian schemes, the uncoherated sheafy trace map is an
isomorphism when its first argument is bounded above with coherent cohomology and its second
argument is bounded below. -/
theorem uncoheratedSheafyTraceMapIsIsoOfProper
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y)
    [hL_boundedAbove : Fact ((t.minus : ObjectProperty
      (RingedSpace.ModuleDerived X.toRingedSpace)) L.obj)]
    [hL_coherent : Fact (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L.obj)]
    [hK_boundedBelow : Fact ((t.plus : ObjectProperty
      (RingedSpace.ModuleDerived Y.toRingedSpace)) K.obj)] :
    IsIso (uncoheratedSheafyTraceMap f a adj L K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
