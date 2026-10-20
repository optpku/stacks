/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Homology.CochainComplex.Cokernel
import Mathlib.Tactic.CrossRefAttribute

/-!
# Opcycles as differential cokernels

For integer cochain complexes, the canonical opcycles object in degree `n` and the cokernel of the
incoming differential are two colimit presentations of the same parallel pair.  This leaf exposes
their canonical comparison without specializing to modules, flatness, or Tor amplitude.
@stack 0653
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Stacks `0653`: the canonical opcycles object in degree `n` is the cokernel of the incoming differential into
that degree. -/
@[stacks 0653 "opcycles as a differential cokernel"]
noncomputable def opcyclesIsoCokernel
    (K : CochainComplex C ℤ) (n : ℤ) :
    K.opcycles n ≅ K.differentialCokernel n :=
  IsColimit.coconePointUniqueUpToIso
    (K.opcyclesIsCokernel (i := n - 1) (j := n) (CochainComplex.prev ℤ n))
    (colimit.isColimit (parallelPair (K.d (n - 1) n) 0))

/-- Stacks `0653`: the canonical opcycles-to-cokernel comparison identifies their quotient projections. -/
@[reassoc (attr := simp), stacks 0653 "opcycles-to-cokernel projection comparison"]
theorem pOpcycles_opcyclesIsoCokernel_hom
    (K : CochainComplex C ℤ) (n : ℤ) :
    K.pOpcycles n ≫ (K.opcyclesIsoCokernel n).hom =
      cokernel.π (K.d (n - 1) n) := sorry

/-- Stacks `0653`: the inverse canonical comparison identifies the cokernel projection with `pOpcycles`. -/
@[reassoc (attr := simp), stacks 0653 "cokernel-to-opcycles projection comparison"]
theorem π_opcyclesIsoCokernel_inv
    (K : CochainComplex C ℤ) (n : ℤ) :
    cokernel.π (K.d (n - 1) n) ≫ (K.opcyclesIsoCokernel n).inv =
      K.pOpcycles n := sorry

/-- Stacks `0653`: the canonical opcycles-to-cokernel comparison is natural in the cochain complex. -/
@[reassoc (attr := simp), stacks 0653 "naturality of the opcycles-to-cokernel comparison"]
theorem opcyclesIsoCokernel_hom_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (K.opcyclesIsoCokernel n).hom ≫ differentialCokernelMap f n =
      HomologicalComplex.opcyclesMap f n ≫ (L.opcyclesIsoCokernel n).hom := sorry

end CochainComplex
