/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.Retraction.Localization
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.Extension.Cotangent.FreeGenerators

/-!
# Smoothing retractions

This leaf owns the presentation-independent smoothing retraction attached to a
finitely presented algebra.  Localized maps are expressed as ring-hom
properties, avoiding temporary localized algebra instances.
-/

@[expose] public section

universe u v w

namespace Algebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

namespace RetractExtension

/-- A finite-type retract equipped with compatible smoothing data on every
principal localization. -/
@[stacks 07CE "smoothing retract extension"]
structure Smoothing (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] where
  /-- The underlying retract extension. -/
  base : RetractExtension.{u, v, w} R A
  /-- The retract extension is of finite type over the source algebra. -/
  [finiteType : Algebra.FiniteType A base.carrier]
  /-- A local complete-intersection chart becomes smooth on the corresponding
  principal localization of the retract extension. -/
  smoothAway (a : A)
      [completeIntersection :
        (algebraMap R (Localization.Away a)).IsLocalCompleteIntersection] :
    (base.awayMap a).toRingHom.Smooth
  /-- A local complete-intersection chart has a chosen finite free cotangent
  generator family after passing to the retract extension. -/
  chart (a : A)
      [completeIntersection :
        (algebraMap R (Localization.Away a)).IsLocalCompleteIntersection] :
    Algebra.FreeCotangentGenerators.{u, w, 0} R
      (Localization.Away (algebraMap A base.carrier a))
  /-- Smooth principal localizations of the source have free Kähler
  differentials after passing to the retract extension. -/
  freeKaehler (a : A) [smooth : Smooth R (Localization.Away a)] :
    Module.Free (Localization.Away (algebraMap A base.carrier a))
      Ω[Localization.Away (algebraMap A base.carrier a)⁄R]

attribute [instance] Smoothing.finiteType

namespace Smoothing

/-- Build smoothing data on a fixed retract extension from its localized
smoothness, cotangent charts, and Kähler freeness properties. -/
def of (E : RetractExtension.{u, v, w} R A) [Algebra.FiniteType A E.carrier]
    (smoothAway : ∀ (a : A)
      [(algebraMap R (Localization.Away a)).IsLocalCompleteIntersection],
        (E.awayMap a).toRingHom.Smooth)
    (chart : ∀ (a : A)
      [(algebraMap R (Localization.Away a)).IsLocalCompleteIntersection],
        Algebra.FreeCotangentGenerators.{u, w, 0} R
          (Localization.Away (algebraMap A E.carrier a)))
    (freeKaehler : ∀ (a : A) [Smooth R (Localization.Away a)],
      Module.Free (Localization.Away (algebraMap A E.carrier a))
        Ω[Localization.Away (algebraMap A E.carrier a)⁄R]) :
    Smoothing R A where
  base := E
  finiteType := inferInstance
  smoothAway := smoothAway
  chart := chart
  freeKaehler := freeKaehler

/-- The retract extension supplied to `Smoothing.of` is recovered by projection. -/
@[simp]
theorem base_of (E : RetractExtension.{u, v, w} R A)
    [Algebra.FiniteType A E.carrier]
    (smoothAway : ∀ (a : A)
      [(algebraMap R (Localization.Away a)).IsLocalCompleteIntersection],
        (E.awayMap a).toRingHom.Smooth)
    (chart : ∀ (a : A)
      [(algebraMap R (Localization.Away a)).IsLocalCompleteIntersection],
        Algebra.FreeCotangentGenerators.{u, w, 0} R
          (Localization.Away (algebraMap A E.carrier a)))
    (freeKaehler : ∀ (a : A) [Smooth R (Localization.Away a)],
      Module.Free (Localization.Away (algebraMap A E.carrier a))
        Ω[Localization.Away (algebraMap A E.carrier a)⁄R]) :
    (Smoothing.of E smoothAway chart freeKaehler).base = E := sorry

/-- The defining finite-type, localized smoothness, cotangent generators,
and Kähler freeness properties of a smoothing retract extension. -/
theorem spec (S : Smoothing.{u, v, w} R A) :
    Algebra.FiniteType A S.base.carrier ∧
      (∀ a : A,
        (algebraMap R (Localization.Away a)).IsLocalCompleteIntersection →
          (S.base.awayMap a).toRingHom.Smooth ∧
            ∃ n : ℕ, ∃ P : Generators R
              (Localization.Away (algebraMap A S.base.carrier a)) (Fin n),
              Module.Free (Localization.Away (algebraMap A S.base.carrier a))
                P.toExtension.Cotangent) ∧
      (∀ a : A,
        Smooth R (Localization.Away a) →
          Module.Free (Localization.Away (algebraMap A S.base.carrier a))
            Ω[Localization.Away (algebraMap A S.base.carrier a)⁄R]) := sorry

/-- Lemma 16.3.1 (tag 07CE): a finitely presented algebra admits a finite-type
smoothing retract extension with compatible localized cotangent data. -/
@[stacks 07CE]
theorem nonempty [FinitePresentation R A] :
    Nonempty (Smoothing.{u, v, max u v} R A) := sorry

end Smoothing

end RetractExtension

end Algebra
