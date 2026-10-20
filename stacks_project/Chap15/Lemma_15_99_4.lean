/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.HomComplex
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom

/-!
# Lemma 15.99.4

This repository retains the earlier section numbering; the mathematical item is Stacks tag
`0BYQ`, Lemma 15.100.4 in the current numbering.  K-flatness is owned by the Hom-complex leaf,
while representation of canonical `RHom` is an existing stronger projective-minus theorem.

@stack 0BYQ
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CochainComplex.ProjectiveMinus

variable {R : Type u} [CommRing R]

/- @stack 0BYQ -/
@[stacks 0BYQ "Lemma 15.99.4 (1): K-flat Hom complex"]
#check fun (P : CochainComplex.ProjectiveMinus (ModuleCat.{u} R))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.IsKFlat)
    (hP : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P :
      CochainComplex (ModuleCat.{u} R) ℤ))) ↦
  (homComplex_isKFlat_of_isPerfect P K hK hP :
    (CochainComplex.HomComplex.moduleComplex R P K).IsKFlat)

/- @stack 0BYQ -/
@[stacks 0BYQ "Lemma 15.99.4 (2): Hom complex represents RHom"]
#check fun [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := R)]
    (P : CochainComplex.ProjectiveMinus (ModuleCat.{u} R))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.IsKFlat)
    (hP : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P :
      CochainComplex (ModuleCat.{u} R) ℤ))) ↦
  (CochainComplex.ProjectiveMinus.representsRHom P K :
    IsIsomorphic
      (DerivedCategory.Q.obj (CochainComplex.HomComplex.moduleComplex R P K))
      (CategoryTheory.DerivedCategory.InternalHom.RHom.obj
        (A := R) (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)))

#check @CochainComplex.ProjectiveMinus.representsRHom

end CochainComplex.ProjectiveMinus
