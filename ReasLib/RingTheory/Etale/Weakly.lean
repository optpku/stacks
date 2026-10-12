/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication
public import ReasLib.RingTheory.Unramified.TensorSquare

/-!
# Explicit-proof API for weakly etale algebras

Mathlib owns `Algebra.WeaklyEtale` and its canonical typeclass instances.  This file adds a small
explicit-proof interface for downstream arguments where installing a local instance would obscure
the mathematical dependency.
@stack 092B
@stack 092H
@stack 092J
@stack 092M
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.WeaklyEtale

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An explicit weakly etale witness supplies module flatness without installing an instance. -/
@[stacks 092B "explicit module-flatness projection"]
theorem toModuleFlat (h : Algebra.WeaklyEtale R S) : Module.Flat R S := by
  letI : Algebra.WeaklyEtale R S := h
  infer_instance

/-- An explicit weakly etale witness supplies flatness of the shared tensor-square multiplication
map. -/
@[stacks 092B "explicit tensor-square flatness projection"]
theorem tensorSquare_flat (h : Algebra.WeaklyEtale R S) :
    (Algebra.tensorSquareMultiplication R S).Flat := by
  letI : Algebra.WeaklyEtale R S := h
  simpa only [Algebra.tensorSquareMultiplication] using
    Algebra.WeaklyEtale.flat_lmul' R S

/-- The algebra map of a weakly etale algebra is flat. -/
@[stacks 092B "explicit algebra-map flatness projection"]
theorem algebraMap_flat (h : Algebra.WeaklyEtale R S) : (algebraMap R S).Flat :=
  RingHom.flat_algebraMap_iff.mpr (toModuleFlat h)

/-- A weakly etale algebra is formally unramified, in explicit-witness form. -/
@[stacks 092M "weakly etale algebras are formally unramified"]
theorem formallyUnramified (h : Algebra.WeaklyEtale R S) :
    Algebra.FormallyUnramified R S :=
  Algebra.FormallyUnramified.of_tensorSquareMul_flat (tensorSquare_flat h)

/-- Weakly etale algebras are stable under base change, in explicit-witness form. -/
@[stacks 092H "weakly etale base change"]
theorem baseChange {T : Type w} [CommRing T] [Algebra R T]
    (h : Algebra.WeaklyEtale R S) : Algebra.WeaklyEtale T (T ⊗[R] S) := by
  letI : Algebra.WeaklyEtale R S := h
  infer_instance

/-- Weakly etale algebra maps are stable under composition, in explicit-witness form. -/
@[stacks 092J "composition of weakly etale maps"]
theorem comp {T : Type w} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (hRS : Algebra.WeaklyEtale R S)
    (hST : Algebra.WeaklyEtale S T) : Algebra.WeaklyEtale R T := by
  letI : Algebra.WeaklyEtale R S := hRS
  letI : Algebra.WeaklyEtale S T := hST
  exact Algebra.WeaklyEtale.trans R S T

end Algebra.WeaklyEtale
