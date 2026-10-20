/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Flat
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.BoundedAbove
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-above K-flat complexes on ringed spaces

@stack 06YD

The categorical criterion `HomologicalComplex.IsTermwiseFlat.isKFlat_of_boundedAbove` is the
reusable owner.  These two declarations keep the
ringed-space surface source-friendly while exposing only the canonical boundedness and flatness
predicates.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex.IsTermwiseFlat

variable {X : RingedSpace.{u}}

/-- Lemma 20.26.9 (06YD): a bounded-above termwise-flat complex of `𝒪_X`-modules is K-flat. -/
@[stacks 06YD "bounded-above termwise-flat complexes are K-flat"]
theorem isKFlat_of_boundedAbove
    {K : CochainComplex (Modules X) ℤ}
    (hFlat : HomologicalComplex.IsTermwiseFlat K)
    (hbounded : CochainComplex.minus (Modules X) K) :
    K.IsKFlat := sorry

/-- Lemma 20.26.9 (06YD), flat-sheaf form: degreewise flat terms give a K-flat complex. -/
@[stacks 06YD "bounded-above flat complexes are K-flat"]
theorem isKFlat_of_boundedAbove_of_flat
    {K : CochainComplex (Modules X) ℤ}
    (hFlat : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n))
    (hbounded : CochainComplex.minus (Modules X) K) :
    K.IsKFlat := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex.IsTermwiseFlat

end
