/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Triangulated
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open SheafOfModules.RingedSite.TensorWithObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}
variable (K : Complex (J := J) (O := O))

/- Lemma 22.35.2 (09LW): the concrete DG tensor functor associated to `K` induces a
triangulated functor to the standard homotopy category of complexes of module sheaves. -/
@[stacks 09LW] #check
  (homotopyFunctor_isTriangulated K :
    (homotopyFunctor K).IsTriangulatedWith (homotopyFunctor_commShift K))

#check @homotopyFunctor
#check @homotopyCommShiftIso
