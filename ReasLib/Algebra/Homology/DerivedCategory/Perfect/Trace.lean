/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective.KProjective
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective.Trace
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect

/-!
# Traces of perfect derived objects

The trace in the additive commutator quotient is computed from any bounded
finite-projective representative and any representing chain map.
-/

public section

noncomputable section

universe u

open CategoryTheory
open scoped Ring

namespace DerivedCategory.IsPerfect

variable {R : Type u} [Ring R]

/-- The trace obtained by lifting a conjugated derived endomorphism to a
bounded finite-projective representative. -/
private noncomputable def traceNaturalOnModel
    (P : CochainComplex (ModuleCat R) ℤ) [hP : P.IsBoundedFiniteProjective]
    {K : DerivedCategory (ModuleCat R)} (e : DerivedCategory.Q.obj P ≅ K)
    (f : End K) : R♮ :=
  let g := e.hom ≫ f ≫ e.inv
  let iso := DerivedCategory.quotientCompQhIso (ModuleCat R)
  let g' := iso.hom.app P ≫ g ≫ iso.inv.app P
  let hmap := Function.surjInv
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient _ _).obj P)).surjective g'
  let fP := (HomotopyCategory.quotient _ _).preimage hmap
  CochainComplex.IsBoundedFiniteProjective.traceNatural fP

/-- The trace of an endomorphism of a perfect object of `D(R)`, with values in
`R♮`. -/
noncomputable def traceNatural {K : DerivedCategory (ModuleCat R)}
    (hK : DerivedCategory.IsPerfect K) (f : End K) : R♮ :=
  let P := hK.choose
  let e := hK.choose_spec.choose.symm
  traceNaturalOnModel P (hP := hK.choose_spec.choose_spec) e f

/-- The trace of a perfect derived endomorphism equals the alternating trace of
every representing endomorphism of a bounded finite-projective complex. -/
theorem traceNatural_spec
    {K : DerivedCategory (ModuleCat R)} (hK : DerivedCategory.IsPerfect K)
    (f : End K) (P : CochainComplex (ModuleCat R) ℤ)
    [P.IsBoundedFiniteProjective] (e : DerivedCategory.Q.obj P ≅ K)
    (fP : P ⟶ P) (hfP : DerivedCategory.Q.map fP = e.hom ≫ f ≫ e.inv) :
    hK.traceNatural f =
      CochainComplex.IsBoundedFiniteProjective.traceNatural fP := sorry

end DerivedCategory.IsPerfect
