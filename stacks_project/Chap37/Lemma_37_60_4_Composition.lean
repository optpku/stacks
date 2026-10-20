/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Composition

@[expose] public section

open CategoryTheory

universe u

#check (RingHom.IsPseudoCoherentRingMap.stableUnderComposition :
  RingHom.StableUnderComposition (@RingHom.IsPseudoCoherentRingMap))

#check (RingHom.IsPseudoCoherentRingMap.comp :
  ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) [f.IsPseudoCoherentRingMap]
    [g.IsPseudoCoherentRingMap], (g.comp f).IsPseudoCoherentRingMap)

#check (AlgebraicGeometry.PseudoCoherent.instIsStableUnderComposition :
  MorphismProperty.IsStableUnderComposition (@AlgebraicGeometry.PseudoCoherent.{u}))

#check (AlgebraicGeometry.PseudoCoherent.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.PseudoCoherent f] [AlgebraicGeometry.PseudoCoherent g],
    AlgebraicGeometry.PseudoCoherent (f ≫ g))
