/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Smooth.EssSmooth
import StacksCheckRecall

@[expose] public section

universe u v

section Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- The essentially smooth algebra predicate used in Lemma 23.10.1 (0FCW); its localization
presentation is exposed separately below. -/
@[stacks 0FCW "essentially smooth algebra predicate"] #check (Algebra.EssSmooth R S : Prop)

end Algebra

section RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable (f : R →+* S)

/- The corresponding map-first predicate uses the algebra structure induced by the map. -/
@[stacks 0FCW "essentially smooth ring-map predicate"] #check (f.EssSmooth : Prop)

end RingHom

#check @Algebra.essSmooth_iff_exists_smooth
#check @Algebra.essSmooth_iff_formallySmooth_and_essFinitePresentation
#check @Algebra.EssSmooth.formallySmooth
#check @Algebra.EssSmooth.essFinitePresentation
#check @Algebra.EssSmooth.flat
#check @Algebra.EssSmooth.of_isLocalization
#check @RingHom.essSmooth_algebraMap
#check @RingHom.essSmooth_def
#check @RingHom.essSmooth_iff_exists_smooth
#check @RingHom.EssSmooth.of_smooth
#check @RingHom.EssSmooth.of_isLocalization
#check @RingHom.EssSmooth.formallySmooth
#check @RingHom.EssSmooth.essFinitePresentation
#check @RingHom.EssSmooth.flat
#check @RingHom.EssSmooth.comp
#check @RingHom.EssSmooth.holdsForLocalizationAway
#check @RingHom.EssSmooth.id
#check @RingHom.EssSmooth.isStableUnderBaseChange
#check @RingHom.EssSmooth.respectsIso
