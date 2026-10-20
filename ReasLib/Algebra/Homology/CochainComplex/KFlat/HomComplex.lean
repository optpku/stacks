/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flatness of Hom complexes

This leaf owns the K-flatness result for the module-valued Hom complex whose source is a
projective-minus representative of a perfect derived object.

@stack 0BYQ
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CochainComplex.ProjectiveMinus

variable {R : Type u} [CommRing R]

/-- Lemma 15.99.4 (1): if `P` is projective-minus and perfect in `D(R)`, then the Hom complex from
`P` to a K-flat complex is K-flat.  This is Stacks tag `0BYQ` (Lemma 15.100.4 in the current
numbering). -/
@[stacks 0BYQ "K-flat Hom complex from a perfect projective-minus source"]
theorem homComplex_isKFlat_of_isPerfect
    (P : CochainComplex.ProjectiveMinus (ModuleCat.{u} R))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.IsKFlat)
    (hP : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P :
      CochainComplex (ModuleCat.{u} R) ℤ))) :
    (CochainComplex.HomComplex.moduleComplex R P K).IsKFlat := sorry
/- Proof strategy: choose a bounded finite-projective representative from `hP`, use projectivity
of `P` to upgrade the derived isomorphism to a homotopy equivalence, transport Hom complexes along
that equivalence, identify the finite-projective Hom complex with the tensor product of the dual
complex and `K`, and apply K-flat stability under tensor products and homotopy equivalence. -/

end CochainComplex.ProjectiveMinus
