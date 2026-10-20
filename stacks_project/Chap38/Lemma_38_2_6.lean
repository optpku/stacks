/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TorAmplitude.Henselization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

/- Lemma 38.2.6 (1): Tor amplitude over the scheme stalk, a compatible henselization, and
the strict henselization are equivalent. -/
@[stacks 0DK0]
#check (IsHenselizationOf.torAmplitudeIn_tfae :
  ∀ (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Msh : DerivedCategory (ModuleCat Rsh)) (a b : ℤ),
    List.TFAE [
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Msh a b,
      DerivedCategory.HasTorAmplitudeInOver Rh Msh a b,
      DerivedCategory.HasTorAmplitudeIn Rsh Msh a b])

/- Lemma 38.2.6 (2): under derived base change from the henselization, Tor amplitude of the
henselization object joins the three equivalent conditions for the strict-henselization object. -/
@[stacks 0DK0]
#check (IsHenselizationOf.torAmplitudeIn_tfae_of_baseChange :
  ∀ (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Msh : DerivedCategory (ModuleCat Rsh)) (Mh : DerivedCategory (ModuleCat Rh))
    (eMsh : (Mh ⊗[Rh]^L[Rsh]) ≅ Msh) (a b : ℤ),
    List.TFAE [
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Msh a b,
      DerivedCategory.HasTorAmplitudeInOver Rh Msh a b,
      DerivedCategory.HasTorAmplitudeIn Rsh Msh a b,
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Mh a b,
      DerivedCategory.HasTorAmplitudeIn Rh Mh a b])

/- Lemma 38.2.6 (3): under successive derived base changes from the stalk, Tor amplitude of
the stalk object joins the five equivalent conditions for the two base-changed objects. -/
@[stacks 0DK0]
#check (IsHenselizationOf.torAmplitudeIn_tfae_of_iteratedBaseChange :
  ∀ (S : Scheme.{u}) (s : S)
    (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type u) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Msh : DerivedCategory (ModuleCat Rsh)) (Mh : DerivedCategory (ModuleCat Rh))
    (eMsh : (Mh ⊗[Rh]^L[Rsh]) ≅ Msh)
    (M : DerivedCategory (ModuleCat (S.presheaf.stalk s)))
    (eMh : (M ⊗[S.presheaf.stalk s]^L[Rh]) ≅ Mh) (a b : ℤ),
    List.TFAE [
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Msh a b,
      DerivedCategory.HasTorAmplitudeInOver Rh Msh a b,
      DerivedCategory.HasTorAmplitudeIn Rsh Msh a b,
      DerivedCategory.HasTorAmplitudeInOver (S.presheaf.stalk s) Mh a b,
      DerivedCategory.HasTorAmplitudeIn Rh Mh a b,
      DerivedCategory.HasTorAmplitudeIn (S.presheaf.stalk s) M a b])
