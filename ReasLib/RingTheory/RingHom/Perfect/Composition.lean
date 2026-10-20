/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Perfect.TorDimension
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Composition

/-!
# Composition of perfect ring maps

Perfect ring maps are closed under composition.
-/

@[expose] public section

universe u

namespace RingHom.IsPerfectRingMap

/-- Perfect ring maps are stable under composition. -/
theorem stableUnderComposition :
    RingHom.StableUnderComposition (@RingHom.IsPerfectRingMap) := sorry

/-- The composite of two perfect ring maps is perfect. -/
instance comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) [f.IsPerfectRingMap]
    [g.IsPerfectRingMap] : (g.comp f).IsPerfectRingMap := sorry

end RingHom.IsPerfectRingMap
