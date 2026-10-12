/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing.ProperFlat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Lemma 48.28.7: let `S` be a quasi-compact and quasi-separated scheme and let
`f : X ⟶ S` be a proper flat morphism of finite presentation. The relative dualizing
complex associated to a chosen right adjoint of derived quasicoherent pushforward,
together with the chosen diagonal-adjunction isomorphism, is a relative dualizing complex. -/
@[stacks 0E2Z] #check
  (AlgebraicGeometry.Scheme.RelativeDualizingComplex.ofDerivedQCoh :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [CompactSpace S] [QuasiSeparatedSpace S]
      [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [MonoidalCategory
        (RingedSpace.ModuleDerived (⊤ : (pullback f f).Opens).toScheme.toRingedSpace)]
      [(RingedSpace.moduleDerivedPushforward
        (Scheme.RelativeDualizingComplex.topDiagonal f).toShHom).LaxMonoidal]
      (H : MonoidalClosed
        (RingedSpace.ModuleDerived (⊤ : (pullback f f).Opens).toScheme.toRingedSpace))
      (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
      (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (c : Scheme.DerivedQCoh (⊤ : (pullback f f).Opens).toScheme ⥤
        Scheme.DerivedQCoh X)
      (cAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
        (Scheme.RelativeDualizingComplex.topDiagonal f) ⊣ c)
      (e : Scheme.DerivedQCoh.structureSheaf X ≅
        c.obj ((Scheme.DerivedQCoh.pullback
          ((⊤ : (pullback f f).Opens).ι ≫ pullback.fst f f)).obj
            (Scheme.DerivedQCoh.relativeDualizingComplex f a aAdjunction))),
      Scheme.RelativeDualizingComplex f (⊤ : (pullback f f).Opens)
        (Scheme.RelativeDualizingComplex.topDiagonal f)
        (Scheme.RelativeDualizingComplex.topDiagonal_comp_ι f) H)
