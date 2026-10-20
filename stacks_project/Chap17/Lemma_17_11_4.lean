/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import StacksCheckRecall

/-!
# Lemma 17.11.4

The two source clauses are ringed-space specializations of the generic kernel theorem for a
surjection onto a finitely presented module sheaf.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

section FiniteFree

variable {F : X.Modules} [F.IsFinitePresentation]
variable (r : ℕ) (f : freeFin (𝒪 := X.ringCatSheaf) r ⟶ F) [Epi f]

/- Lemma 17.11.4 (01BP), first clause: the kernel of a surjection from a finite-rank free module
sheaf to a finitely presented module sheaf is finite type. -/
@[stacks 01BP "(1)"]
#check
  (IsFinitePresentation.kernel_of_epi f :
    (kernel f).IsFiniteType)

end FiniteFree

section FiniteType

variable {G F : X.Modules} (f : G ⟶ F)
variable [Epi f] [G.IsFiniteType] [F.IsFinitePresentation]

/- Lemma 17.11.4 (01BP), second clause: the kernel of a surjection from a finite-type module
sheaf to a finitely presented module sheaf is finite type. -/
@[stacks 01BP "(2)"]
#check
  (IsFinitePresentation.kernel_of_epi f :
    (kernel f).IsFiniteType)

end FiniteType

end SheafOfModules
