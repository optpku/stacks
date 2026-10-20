module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Proper
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open DerivedCategory.TStructure
open CategoryTheory.MonoidalClosed
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

universe u

/- Example 48.3.9: for a proper morphism `f : X ⟶ Y` of Noetherian schemes,
`L ∈ D⁻_Coh(X)`, and `K ∈ D⁺_QCoh(𝒪_Y)`, the uncoherated sheafy trace map
from `Rf_* RHom(L, a(K))` to `RHom(Rf_* L, K)` is an isomorphism. -/
@[stacks 0GEW] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.uncoheratedSheafyTraceMapIsIsoOfProper :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [IsNoetherian X] [IsNoetherian Y] [IsProper f]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X)
      (adj : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (L : AlgebraicGeometry.Scheme.DerivedQCoh X)
      (K : AlgebraicGeometry.Scheme.DerivedQCoh Y)
      [Fact ((t.minus : ObjectProperty
        (RingedSpace.ModuleDerived X.toRingedSpace)) L.obj)]
      [Fact (DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L.obj)]
      [Fact ((t.plus : ObjectProperty
        (RingedSpace.ModuleDerived Y.toRingedSpace)) K.obj)],
      IsIso (AlgebraicGeometry.Scheme.DerivedQCoh.uncoheratedSheafyTraceMap
        f a adj L K))
