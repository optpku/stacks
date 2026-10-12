/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing.Pairing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Remark 48.12.6: a relative pairing with pseudo-coherent second factor whose curry is
invertible induces, by relative cup product and the dualizing trace, an invertible curried
pairing after derived pushforward. -/
@[stacks 0G81] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeCupProductTraceCurryIsIso :
    ∀ {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
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
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (K M : DerivedQCoh X)
      (pairing : K.obj ⊗ M.obj ⟶ (relativeDualizingComplex f a aAdjunction).obj)
      [Fact (RingedSpace.ModuleDerived.IsPseudoCoherent M.obj)]
      [IsIso (braidedHomEquiv K.obj M.obj
        (relativeDualizingComplex f a aAdjunction).obj pairing)],
      IsIso
        (braidedHomEquiv
          ((RingedSpace.moduleDerivedPushforward f.toShHom).obj K.obj)
          ((RingedSpace.moduleDerivedPushforward f.toShHom).obj M.obj)
          (structureSheaf Y).obj
          (@RingedSite.Hom.modulePushforwardDerived.cupProduct _ _
              (RingedSpace.opensRingedSiteHom f.toShHom) _ _ _ _ _ _ _ _
              (Functor.Monoidal.toOplaxMonoidal
                (F := RingedSpace.modulePullbackDerived f.toShHom)) K.obj M.obj ≫
            (RingedSpace.moduleDerivedPushforward f.toShHom).map pairing ≫
            (pushforwardCohomologyIn.inclusionIso f).inv.app
              (relativeDualizingComplex f a aAdjunction) ≫
            (inclusion Y).map (relativeDualizingTrace f a aAdjunction))))

end AlgebraicGeometry.Scheme.DerivedQCoh
