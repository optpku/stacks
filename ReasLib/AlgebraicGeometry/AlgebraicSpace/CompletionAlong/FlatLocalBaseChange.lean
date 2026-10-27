/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.AffineBaseChange
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Flat local base change away from the closed point

Flat local base change preserving the maximal ideal and inducing a bijection
on residue fields gives an equivalence on locally finite type algebraic spaces
that are isomorphisms away from the closed point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- A flat local map of local Noetherian rings preserving the maximal ideal
and inducing a bijection on residue fields gives an equivalence by canonical
base change on locally finite type algebraic spaces that are isomorphisms
away from the closed point. The hypothesis `hmax` identifies the extended
ideal used in the target of the functor with the maximal ideal of `B`.
The morphism `hA` allows these spaces to be considered over an ambient scheme. -/
theorem isEquivalence_sourceBaseChangeAlgebraMap_of_flat {A : Type u}
    (B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing A]
    [IsNoetherianRing B] [Module.Flat A B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S)
    (hmax : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (hresidue : Function.Bijective (ResidueField.map (algebraMap A B))) :
    (sourceBaseChangeAlgebraMap B hA (maximalIdeal A)).IsEquivalence :=
  sorry

/-- Canonical base change along a flat local map of local Noetherian rings
is an equivalence away from the closed point when preservation of the maximal
ideal and bijectivity of the induced residue-field map are available as facts. -/
instance instIsEquivalenceSourceBaseChangeAlgebraMapOfFlat {A : Type u}
    (B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
    [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing A]
    [IsNoetherianRing B] [Module.Flat A B] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S)
    [Fact ((maximalIdeal A).map (algebraMap A B) = maximalIdeal B)]
    [Fact (Function.Bijective (ResidueField.map (algebraMap A B)))] :
    (sourceBaseChangeAlgebraMap B hA (maximalIdeal A)).IsEquivalence :=
  isEquivalence_sourceBaseChangeAlgebraMap_of_flat B hA Fact.out Fact.out

end AlgebraicGeometry.AlgebraicSpace.completionAlong
