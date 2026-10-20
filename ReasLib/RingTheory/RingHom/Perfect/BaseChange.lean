/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.ModuleExtension
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.RingHom.Perfect.Basic
public import ReasLib.RingTheory.RingHom.PseudoCoherent.BaseChange

/-!
# Flat base change of perfect ring maps

Finite Tor dimension and perfectness of commutative ring maps are preserved by tensor-product
base change along a flat algebra.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u

namespace RingHom.HasFiniteTorDimension

/-- A commutative ring map of finite Tor dimension retains finite Tor dimension after
tensor-product base change along a flat commutative algebra. -/
theorem baseChange_of_flat
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A']
    (hB : (algebraMap A B).HasFiniteTorDimension)
    (hA' : (algebraMap A A').Flat) :
    (algebraMap A' (B ⊗[A] A')).HasFiniteTorDimension := sorry

end RingHom.HasFiniteTorDimension

namespace RingHom.IsPerfectRingMap

/-- A perfect commutative ring map remains perfect after tensor-product base change along a
flat commutative algebra. -/
theorem baseChange_of_flat
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A']
    (hB : (algebraMap A B).IsPerfectRingMap)
    (hA' : (algebraMap A A').Flat) :
    (algebraMap A' (B ⊗[A] A')).IsPerfectRingMap := sorry

end RingHom.IsPerfectRingMap
