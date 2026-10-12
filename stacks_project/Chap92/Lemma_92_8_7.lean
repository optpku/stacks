/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent complex of (strict) henselizations

For a local homomorphism of local rings `A → B`, the transitivity maps identify
`L_{Bh/Ah}` and `L_{Bh/A}` with `L_{B/A} ⊗^L_B Bh` in `D(Bh)`, and likewise
for strict henselizations in `D(Bsh)`.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory

universe u

namespace Algebra.CotangentComplex

/-- Lemma 92.8.7 (1). Let `A → B` be a local homomorphism of local rings, and let
`Ah`, `Bh` be henselizations of `A` and `B` with an induced map `Ah → Bh`. Then
`L_{Bh/A} = L_{B/A} ⊗^L_B Bh` in `D(Bh)`, as invertibility of
`tensorMap A B Bh : tensor A B Bh ⟶ derived A Bh`. -/
@[stacks 08UN]
theorem tensorMap_isIso_of_isHenselization (A B Ah Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ah] [IsHenselizationOf A Ah] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [Algebra Ah Bh] [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] :
    IsIso (tensorMap A B Bh) :=
  sorry

/-- Lemma 92.8.7 (2). Let `A → B` be a local homomorphism of local rings, and let
`Ah`, `Bh` be henselizations of `A` and `B` with an induced map `Ah → Bh`. Then
`L_{Bh/Ah} = L_{Bh/A}` in `D(Bh)`, as invertibility of
`toRelativeMap A Ah Bh : derived A Bh ⟶ derived Ah Bh`. -/
@[stacks 08UN]
theorem toRelativeMap_isIso_of_isHenselization (A B Ah Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ah] [IsHenselizationOf A Ah] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [Algebra Ah Bh] [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] :
    IsIso (toRelativeMap A Ah Bh) :=
  sorry

/-- Under henselization of a local homomorphism of local rings, the objects
`derived Ah Bh` and `tensor A B Bh` are isomorphic in `D(Bh)`. -/
theorem isIsomorphic_derived_tensor_of_isHenselization (A B Ah Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ah] [IsHenselizationOf A Ah] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [Algebra Ah Bh] [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] :
    IsIsomorphic (derived Ah Bh) (tensor A B Bh) :=
  sorry

/-- Lemma 92.8.7 (3). Let `A → B` be a local homomorphism of local rings, and let
`Ash`, `Bsh` be strict henselizations of `A` and `B` with an induced map
`Ash → Bsh`. Then `L_{Bsh/A} = L_{B/A} ⊗^L_B Bsh` in `D(Bsh)`, as invertibility
of `tensorMap A B Bsh : tensor A B Bsh ⟶ derived A Bsh`. -/
@[stacks 08UN]
theorem tensorMap_isIso_of_isStrictHenselization (A B Ash Bsh : Type u)
    [CommRing A] [CommRing B] [CommRing Ash] [CommRing Bsh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    [Algebra A Bsh] [Algebra Ash Bsh]
    [IsScalarTower A B Bsh] [IsScalarTower A Ash Bsh] :
    IsIso (tensorMap A B Bsh) :=
  sorry

/-- Lemma 92.8.7 (4). Let `A → B` be a local homomorphism of local rings, and let
`Ash`, `Bsh` be strict henselizations of `A` and `B` with an induced map
`Ash → Bsh`. Then `L_{Bsh/Ash} = L_{Bsh/A}` in `D(Bsh)`, as invertibility of
`toRelativeMap A Ash Bsh : derived A Bsh ⟶ derived Ash Bsh`. -/
@[stacks 08UN]
theorem toRelativeMap_isIso_of_isStrictHenselization (A B Ash Bsh : Type u)
    [CommRing A] [CommRing B] [CommRing Ash] [CommRing Bsh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    [Algebra A Bsh] [Algebra Ash Bsh]
    [IsScalarTower A B Bsh] [IsScalarTower A Ash Bsh] :
    IsIso (toRelativeMap A Ash Bsh) :=
  sorry

/-- Under strict henselization of a local homomorphism of local rings, the objects
`derived Ash Bsh` and `tensor A B Bsh` are isomorphic in `D(Bsh)`. -/
theorem isIsomorphic_derived_tensor_of_isStrictHenselization (A B Ash Bsh : Type u)
    [CommRing A] [CommRing B] [CommRing Ash] [CommRing Bsh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    [Algebra A Bsh] [Algebra Ash Bsh]
    [IsScalarTower A B Bsh] [IsScalarTower A Ash Bsh] :
    IsIsomorphic (derived Ash Bsh) (tensor A B Bsh) :=
  sorry

end Algebra.CotangentComplex
