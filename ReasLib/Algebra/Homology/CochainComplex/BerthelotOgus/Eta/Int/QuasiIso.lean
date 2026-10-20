/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int

/-!
# Quasi-isomorphisms and the integer-indexed Berthelot-Ogus eta operator

The divided-differential eta functor preserves quasi-isomorphisms on its canonical domain of
termwise torsion-free complexes.  This is the unbounded, integer-indexed statement needed for the
derived eta functor; the nonnegative version is a specialization rather than the source owner.
@stack 0F7Q
-/

@[expose] public section

open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int

variable {A : Type u} [CommRing A]

/-- The eta map associated to a quasi-isomorphism of termwise `f`-torsion-free integer-indexed
complexes is a quasi-isomorphism. -/
theorem map_quasiIso (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L)
    [QuasiIso φ] (hK : IsTermwiseTorsionFree f K)
    (hL : IsTermwiseTorsionFree f L) : QuasiIso (map f φ hK hL) := sorry

/-- Lemma 15.96.3, tag `0F7Q`: the divided-differential eta functor preserves
quasi-isomorphisms between complexes of modules on which a nonzerodivisor acts termwise
regularly. -/
@[stacks 0F7Q "Berthelot-Ogus eta preserves quasi-isomorphisms", instance]
theorem functor_map_quasiIso (f : nonZeroDivisors A) {K L : Domain (f : A)}
    (φ : K ⟶ L) [QuasiIso φ.hom] : QuasiIso ((functor (f : A)).map φ) := sorry

end CochainComplex.BerthelotOgus.Int
