/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Relative
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Henselization
public import ReasLib.RingTheory.Henselian.FaithfullyFlat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

namespace IsHenselizationOf

/-- The Tor amplitude of an object over a strict henselization of a scheme stalk is
equivalent when measured over the stalk, a compatible henselization, or the strict
henselization itself. -/
@[stacks 0DK0]
theorem torAmplitudeIn_tfae (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Msh : DerivedCategory (ModuleCat Rsh)) (a b : ℤ) :
    List.TFAE [
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Msh a b,
      DerivedCategory.HasTorAmplitudeInOver Rh Msh a b,
      DerivedCategory.HasTorAmplitudeIn Rsh Msh a b] := sorry

/-- If an object over a strict henselization is obtained by derived base change from a
henselization, the two Tor-amplitude conditions before base change join the three equivalent
conditions after base change. -/
@[stacks 0DK0]
theorem torAmplitudeIn_tfae_of_baseChange (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Msh : DerivedCategory (ModuleCat Rsh)) (Mh : DerivedCategory (ModuleCat Rh))
    (eMsh : (Mh ⊗[Rh]^L[Rsh]) ≅ Msh) (a b : ℤ) :
    List.TFAE [
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Msh a b,
      DerivedCategory.HasTorAmplitudeInOver Rh Msh a b,
      DerivedCategory.HasTorAmplitudeIn Rsh Msh a b,
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Mh a b,
      DerivedCategory.HasTorAmplitudeIn Rh Mh a b] := sorry

/-- For objects obtained by successive derived base changes from a scheme stalk through a
compatible henselization to a strict henselization, Tor amplitude of the original object is
equivalent to Tor amplitude of either base-changed object over each relevant ring. -/
@[stacks 0DK0]
theorem torAmplitudeIn_tfae_of_iteratedBaseChange (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Msh : DerivedCategory (ModuleCat Rsh)) (Mh : DerivedCategory (ModuleCat Rh))
    (eMsh : (Mh ⊗[Rh]^L[Rsh]) ≅ Msh)
    (M : DerivedCategory (ModuleCat (S.presheaf.stalk s)))
    (eMh : (M ⊗[S.presheaf.stalk s]^L[Rh]) ≅ Mh) (a b : ℤ) :
    List.TFAE [
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Msh a b,
      DerivedCategory.HasTorAmplitudeInOver Rh Msh a b,
      DerivedCategory.HasTorAmplitudeIn Rsh Msh a b,
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Mh a b,
      DerivedCategory.HasTorAmplitudeIn Rh Mh a b,
      DerivedCategory.HasTorAmplitudeIn (S.presheaf.stalk s) M a b] := sorry

end IsHenselizationOf
