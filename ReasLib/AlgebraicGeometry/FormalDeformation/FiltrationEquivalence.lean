/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Along

/-!
# Equivalence of completion fibres

The comparison functor associated to a cofinal ideal filtration identifies the
filtration-indexed formal-object category with the completion fibre.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject.Along

/-- The comparison functor from a cofinal filtration is an equivalence. -/
theorem toFiber_isEquivalence (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k)
    (I : CompleteLocalAlgCat.AdicIdealFiltration R) :
    -- Local instance justification (defeq pin): IsEquivalence must use the explicit source category stored in the comparison functor.
    letI := category (p := p) (R := R) (I := I)
    (toFiber p R I).IsEquivalence := sorry

end FormalObject.Along
