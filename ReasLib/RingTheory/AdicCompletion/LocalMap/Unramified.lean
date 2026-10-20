/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Unramified.LocalRing
public import ReasLib.RingTheory.AdicCompletion.LocalMap.Finite
public import ReasLib.RingTheory.AdicCompletion.LocalMap.LocalHom
public import ReasLib.RingTheory.RingHom.Unramified

/-!
# Unramified local maps on maximal-ideal completions

Completion invariance, finiteness, and surjectivity consequences for the map on
maximal-ideal completions induced by a formally unramified local homomorphism.
-/

@[expose] public section

open Ideal IsLocalRing

universe u v

namespace AdicCompletion.LocalMap

/-- An essentially finite type, formally unramified local homomorphism of
Noetherian local rings induces a finite module on maximal-ideal completions. -/
theorem finite_of_formallyUnramified
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra.FormallyUnramified A B] :
    @Module.Finite
      (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal B) B)
      inferInstance inferInstance
      (AdicCompletion.mapLocalAlgebra (algebraMap A B)).toModule := sorry

/-- If the residue-field map of an essentially finite type, formally
unramified local homomorphism of Noetherian local rings is bijective, then the
induced map on maximal-ideal completions is surjective. -/
theorem surjective_of_formallyUnramified_of_residueField_bijective
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra.FormallyUnramified A B]
    (h_residue : Function.Bijective (ResidueField.map (algebraMap A B))) :
    Function.Surjective (AdicCompletion.mapLocal (algebraMap A B)) := sorry

/-- If the source residue field is separably closed, an essentially finite
type, formally unramified local homomorphism of Noetherian local rings induces
a surjection on maximal-ideal completions. -/
theorem surjective_of_formallyUnramified_of_isSepClosed
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra.FormallyUnramified A B] [IsSepClosed (ResidueField A)] :
    Function.Surjective (AdicCompletion.mapLocal (algebraMap A B)) := sorry

/-- For an essentially finite type local homomorphism of Noetherian local
rings, formal unramifiedness is equivalent to formal unramifiedness together
with essential finite type of the induced map on maximal-ideal completions,
and to ordinary unramifiedness of that completion map. -/
theorem unramified_tfae
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] (h_essentiallyFiniteType : f.EssFiniteType) :
    List.TFAE [
      f.FormallyUnramified,
      (AdicCompletion.mapLocal f).FormallyUnramified ∧
        (AdicCompletion.mapLocal f).EssFiniteType,
      (AdicCompletion.mapLocal f).Unramified] := sorry

end AdicCompletion.LocalMap
