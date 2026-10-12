/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Weakly.Flat
public import ReasLib.RingTheory.RingHom.Flat.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change, composition, and descent for weakly etale maps

This leaf owns the tensor-square flatness operations and the corresponding weakly-etale
consequences used by the tower lemmas.

@stack 092H
@stack 092J
@stack 092K
@stack 092L
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorSquare

/-- Lemma 15.105.7 (1): flatness of tensor-square multiplication is preserved by base change. -/
@[stacks 092H "tensor-square multiplication flatness under base change"]
theorem flat_baseChange
    {A : Type u} {A' : Type v} {B : Type w}
    [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]
    (h : (Algebra.tensorSquareMultiplication A B).Flat) :
    (Algebra.tensorSquareMultiplication A' (A' ⊗[A] B)).Flat := sorry

/-- Lemma 15.105.9 (1): flat tensor-square multiplication maps compose in an algebra tower. -/
@[stacks 092J "tensor-square multiplication flatness in a tower"]
theorem flat_comp
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hAB : (Algebra.tensorSquareMultiplication A B).Flat)
    (hBC : (Algebra.tensorSquareMultiplication B C).Flat) :
    (Algebra.tensorSquareMultiplication A C).Flat := sorry

/-- Lemma 15.105.10 (1): tensor-square multiplication flatness descends along a faithfully flat
map in an algebra tower. -/
@[stacks 092K "faithfully-flat tensor-square descent"]
theorem flat_of_faithfullyFlat
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hBC : (algebraMap B C).FaithfullyFlat)
    (hAC : (Algebra.tensorSquareMultiplication A C).Flat) :
    (Algebra.tensorSquareMultiplication A B).Flat := sorry

end Algebra.TensorSquare

namespace Algebra.WeaklyEtale

/-- Lemma 15.105.10 (2): weakly-etale structure descends along a faithfully flat map in an
algebra tower. -/
@[stacks 092K "faithfully-flat weakly-etale descent"]
theorem of_faithfullyFlat
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hBC : (algebraMap B C).FaithfullyFlat) (hAC : WeaklyEtale A C) :
    WeaklyEtale A B := sorry

/-- Lemma 15.105.11: an algebra map between weakly-etale algebras over a common base is weakly
etale. -/
@[stacks 092L "weakly-etale tower closure"]
theorem of_tower
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (hAB : WeaklyEtale A B) (hAC : WeaklyEtale A C) :
    WeaklyEtale B C := sorry

end Algebra.WeaklyEtale
