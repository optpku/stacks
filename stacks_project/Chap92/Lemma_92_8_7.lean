/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Henselization
import StacksCheckRecall

/-!
# Cotangent complex of (strict) henselizations

For a local homomorphism of local rings `A → B`, the transitivity maps identify
`L_{Bh/Ah}` and `L_{Bh/A}` with `L_{B/A} ⊗^L_B Bh` in `D(Bh)`, and likewise
for strict henselizations in `D(Bsh)`.
-/

open Algebra.CotangentComplex
open CategoryTheory

universe u

/- Lemma 92.8.7. Henselization of a local homomorphism identifies
`L_{Bh/Ah}` with `L_{B/A} ⊗^L_B Bh` in `D(Bh)`. -/
@[stacks 08UN] #check (Algebra.CotangentComplex.isIsomorphic_derived_tensor_of_isHenselization :
    ∀ (A B Ah Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ah] [IsHenselizationOf A Ah] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [Algebra Ah Bh] [IsScalarTower A B Bh] [IsScalarTower A Ah Bh],
    IsIsomorphic (derived Ah Bh) (tensor A B Bh))

/- The first canonical comparison identifies `L_{Bh/A}` with the derived scalar
extension of `L_{B/A}`. -/
#check (Algebra.CotangentComplex.tensorMap_isIso_of_isHenselization :
    ∀ (A B Bh : Type u) [CommRing A] [CommRing B] [CommRing Bh]
    [IsLocalRing B] [Algebra A B] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [IsScalarTower A B Bh],
    IsIso (tensorMap A B Bh))

/- The second canonical comparison identifies `L_{Bh/Ah}` with `L_{Bh/A}`. -/
#check (Algebra.CotangentComplex.toRelativeMap_isIso_of_isHenselization :
    ∀ (A Ah Bh : Type u) [CommRing A] [CommRing Ah] [CommRing Bh]
    [IsLocalRing A] [Algebra A Ah] [IsHenselizationOf A Ah]
    [Algebra Ah Bh] [Algebra A Bh] [IsScalarTower A Ah Bh],
    IsIso (toRelativeMap A Ah Bh))

/- Strict henselization gives the analogous identification in `D(Bsh)`. -/
#check (Algebra.CotangentComplex.isIsomorphic_derived_tensor_of_isStrictHenselization :
    ∀ (A B Ash Bsh : Type u)
    [CommRing A] [CommRing B] [CommRing Ash] [CommRing Bsh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    [Algebra A Bsh] [Algebra Ash Bsh]
    [IsScalarTower A B Bsh] [IsScalarTower A Ash Bsh],
    IsIsomorphic (derived Ash Bsh) (tensor A B Bsh))

/- The first strict henselization comparison identifies `L_{Bsh/A}` with the
derived scalar extension of `L_{B/A}`. -/
#check (Algebra.CotangentComplex.tensorMap_isIso_of_isStrictHenselization :
    ∀ (A B Bsh : Type u) [CommRing A] [CommRing B] [CommRing Bsh]
    [IsLocalRing B] [Algebra A B] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    [Algebra A Bsh] [IsScalarTower A B Bsh],
    IsIso (tensorMap A B Bsh))

/- The second strict henselization comparison identifies `L_{Bsh/Ash}` with
`L_{Bsh/A}`. -/
#check (Algebra.CotangentComplex.toRelativeMap_isIso_of_isStrictHenselization :
    ∀ (A Ash Bsh : Type u) [CommRing A] [CommRing Ash] [CommRing Bsh]
    [IsLocalRing A] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [Algebra Ash Bsh] [Algebra A Bsh] [IsScalarTower A Ash Bsh],
    IsIso (toRelativeMap A Ash Bsh))
