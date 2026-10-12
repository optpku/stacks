/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Formally Etale Tensor-Product Maps

This leaf owns the map-level stability of formal etaleness under tensor base
change.  It complements mathlib's object-level base-change instance with the
explicit `Algebra.TensorProduct.map` spelling needed by ring-hom consumers.
@stack 0H93
-/

@[expose] public section

universe u v w x

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- Tag `0H93` support: tensoring a formally etale map `S → S'` on the left
with any `S`-algebra `T` gives a formally etale tensor-product map. -/
@[stacks 0H93 "formally etale tensor-product base change"]
theorem map_formallyEtale
    {R : Type u} {S : Type v} {S' : Type w} {T : Type x}
    [CommRing R] [CommRing S] [CommRing S'] [CommRing T]
    [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S S'] :
    (map (AlgHom.id S T) (IsScalarTower.toAlgHom R S S') :
      T ⊗[R] S →+* T ⊗[R] S').FormallyEtale := sorry

end Algebra.TensorProduct
