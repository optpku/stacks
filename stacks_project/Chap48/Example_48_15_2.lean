/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.BaseChange.BlowupCounterexample

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Example 48.15.2 (1) -/
@[stacks 0AAC] #check (AlgebraicGeometry.Scheme.DerivedQCoh.blowupOriginBaseChange_not_isIso :
  (k : Type u) → [Field k] →
    let Y := Spec (CommRingCat.of (PuncturedAffinePlane.coordinateRing k))
    let I := Scheme.idealSheafDataOfIdealOnSpec (PuncturedAffinePlane.originIdeal k)
    ∀ {X : Scheme.{u}} (f : X ⟶ Y) [IsBlowup f I]
      [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
      (f' : (I.comap f).subscheme ⟶ I.subscheme)
      [QuasiCompact f'] [QuasiSeparated f']
      (sq : IsPullback (I.comap f).subschemeι f' f I.subschemeι)
      [LocallyOfType RingHom.IsPerfectRingMap I.subschemeι]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (a' : DerivedQCoh I.subscheme ⥤ DerivedQCoh (I.comap f).subscheme)
      (fAdjunction : pushforwardCohomologyIn f ⊣ a)
      (f'Adjunction : pushforwardCohomologyIn f' ⊣ a')
      (dualBaseChangeIso :
        a' ⋙ pushforwardCohomologyIn (I.comap f).subschemeι ≅
          pushforwardCohomologyIn I.subschemeι ⋙ a)
      (h_dualBaseChange : dualBaseChangeIso.hom =
        BaseChange.rightMate (I.comap f).subschemeι f' f I.subschemeι sq.toCommSq
          a a' fAdjunction f'Adjunction),
      ¬ IsIso
        ((DerivedBaseChange.mapOfRight
          (pullbackPushforwardAdjunction I.subschemeι)
          (pullbackPushforwardAdjunction (I.comap f).subschemeι)
          dualBaseChangeIso.inv).app (structureSheaf Y)))

/- Example 48.15.2 (2) -/
@[stacks 0AAC] #check (AlgebraicGeometry.Scheme.DerivedQCoh.blowupOrigin_not_torIndependent :
  (k : Type u) → [Field k] →
    let Y := Spec (CommRingCat.of (PuncturedAffinePlane.coordinateRing k))
    let I := Scheme.idealSheafDataOfIdealOnSpec (PuncturedAffinePlane.originIdeal k)
    ∀ {X : Scheme.{u}} (f : X ⟶ Y) [IsBlowup f I]
      [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
      [LocallyOfType RingHom.IsPerfectRingMap I.subschemeι],
      ¬ Scheme.TorIndependentOver (Over.mk f) (Over.mk I.subschemeι))

end AlgebraicGeometry.Scheme.DerivedQCoh
