/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Finiteness
public import stacks_project.Chap48.Example_48_3_7
public import stacks_project.Chap48.Lemma_48_3_5
import StacksCheckRecall

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

/- Remark 48.3.8: if both derived internal-Hom objects have quasicoherent
cohomology, then the uncoherated sheafy trace map is an isomorphism. -/
@[stacks 0GEV]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.uncoheratedSheafyTraceMapIsIsoOfDerivedQCoh
    (f := f) :
    ∀ (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforward f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y)
      [h_source : derivedQuasiCoherentModuleProperty X
        ((ihom L.obj).obj (a.obj K).obj)]
      [h_target : derivedQuasiCoherentModuleProperty Y
        ((ihom ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).obj K.obj)],
      IsIso (uncoheratedSheafyTraceMap f a adj L K))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.uncoheratedSheafyTraceMapIsIsoOfPerfect
    (f := f) :
    ∀ (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforward f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y)
      [hL : Fact (RingedSpace.ModuleDerived.IsPerfect L.obj)]
      [hRfL : Fact (RingedSpace.ModuleDerived.IsPerfect
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj))],
      IsIso (uncoheratedSheafyTraceMap f a adj L K))

#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.uncoheratedSheafyTraceMapIsIsoOfPseudoCoherent
    (f := f) :
    ∀ (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforward f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y)
      [hK : Fact ((t.plus : ObjectProperty
        (RingedSpace.ModuleDerived Y.toRingedSpace)) K.obj)]
      [hL : Fact (RingedSpace.ModuleDerived.IsPseudoCoherent L.obj)]
      [hRfL : Fact (RingedSpace.ModuleDerived.IsPseudoCoherent
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj))],
      IsIso (uncoheratedSheafyTraceMap f a adj L K))

end AlgebraicGeometry.Scheme.DerivedQCoh
