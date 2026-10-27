/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CotangentComplex.NaiveComparison.Self
public import ReasLib.RingTheory.CotangentComplex.DerivedExt
public import ReasLib.RingTheory.RingHom.SquareZero.DerivedObstruction

/-!
# Deformations of ring maps and the cotangent complex

The obstruction, translation torsor, and automorphism comparison for a
square-zero deformation are supplied by the full cotangent complex.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory
open Algebra.CotangentComplex RingHom.SquareZeroExtension
open scoped DerivedExt

variable {A' A : Type u} [CommRing A'] [CommRing A]
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (B : Type u) [CommRing B] [Algebra A B]
variable {N : Type u} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
variable (c : KernelModule π →ₗ[A] N)

/- Lemma 92.16.1
The canonical Ext² obstruction vanishes precisely when the square-zero deformation
problem has a solution. Given a solution, its isomorphism classes form a torsor
under Ext¹, and its compatible automorphisms are canonically Ext⁰.
-/
@[stacks 08SP] #check
  (RingHom.SquareZeroExtension.existenceObstructionOf_eq_zero_iff π B c :
    (hq :
      -- Local instance justification (noncanonical choice): Algebra A' A is selected by the explicit square-zero map π.
      letI := algebraOfSquareZero π
      -- Local instance justification (noncanonical choice): Algebra A' B is selected by the composite of π with algebraMap A B.
      letI := algebraCompOfSquareZero π B
      -- Local instance justification (defeq pin): the chosen composite algebra maps identify the tower A' → A → B definitionally.
      letI : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
      QuasiIso (Algebra.CotangentComplex.fromMappingConeCochain A' A B)) →
    existenceObstructionOf π B hq c = 0 ↔
      Nonempty (Solution (B := B) (N := N) π c))

#check (RingHom.SquareZeroExtension.derivedAddTorsorOf π B c :
  (hbij : Function.Bijective (extOneNaiveDerivedHom A B N)) →
  Solution (B := B) (N := N) π c →
    AddTorsor (Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N)) (IsoClass π B c))

#check (RingHom.SquareZeroExtension.autEquiv π B c :
  (S : Solution (B := B) (N := N) π c) →
    Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N) ≃ FittingMap (compare S S))
