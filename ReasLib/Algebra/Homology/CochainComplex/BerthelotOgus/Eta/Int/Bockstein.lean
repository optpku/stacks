/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Reduction
public import ReasLib.Algebra.Homology.HomologicalComplex.Bockstein

/-!
# Comparison from eta reduction to the Bockstein complex

The divided representative of a reduced eta term is a cycle modulo `f`.  Its homology class gives
a canonical morphism from the reduction of the integer-indexed eta complex to the Bockstein
complex of the ambient complex.  The boundary presentation of eta reduction identifies this
morphism as a quasi-isomorphism.

@stack 0F7T
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int

variable {A : Type u} [CommRing A]

/-- The degreewise eta-to-homology maps intertwine the divided eta differential with the
Bockstein differential. -/
@[stacks 0GSP "factorization through the Bockstein operator"]
theorem toHomology_comm_operator
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) (i : ℤ) :
    Reduction.toHomology f K i hK ≫
        HomologicalComplex.Bockstein.operator f K hK i (i + 1)
          (ComplexShape.up_mk i (i + 1) rfl) =
      (Reduction.complex f K hK).d i (i + 1) ≫
        Reduction.toHomology f K (i + 1) hK := sorry

/-- The degreewise eta-to-homology maps commute with every differential component. -/
theorem toHomology_comm
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    Reduction.toHomology f K i hK ≫
        (HomologicalComplex.Bockstein.complex f K hK).d i j =
      (Reduction.complex f K hK).d i j ≫
        Reduction.toHomology f K j hK := sorry

/-- Lemma 15.96.6, tag `0F7T`: the canonical morphism from eta reduction to the Bockstein
cohomology complex. -/
@[stacks 0F7T "eta reduction to the Bockstein complex"]
noncomputable def toBockstein
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    Reduction.complex f K hK ⟶ HomologicalComplex.Bockstein.complex f K hK where
  f i := Reduction.toHomology f K i hK
  comm' i j hij := toHomology_comm f K hK i j hij

/-- The component of the eta-to-Bockstein comparison is the canonical map to homology modulo
`f`. -/
@[simp]
theorem toBockstein_f
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) (i : ℤ) :
    (toBockstein f K hK).f i = Reduction.toHomology f K i hK := sorry

/-- The eta-to-Bockstein comparison is a quasi-isomorphism whenever `f` acts regularly on every
term. -/
theorem toBockstein_quasiIso
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    QuasiIso (toBockstein f K hK) := sorry

/-- Lemma 15.96.6, tag `0F7T`: for a nonzerodivisor `f` and a complex of `f`-torsion-free
modules, the canonical map from eta reduction to the Bockstein complex is a quasi-isomorphism. -/
@[stacks 0F7T "eta reduction is quasi-isomorphic to the Bockstein complex"]
theorem toBockstein_quasiIso_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseTorsionFree f K) :
    QuasiIso (toBockstein f K hK) := sorry

end CochainComplex.BerthelotOgus.Int
