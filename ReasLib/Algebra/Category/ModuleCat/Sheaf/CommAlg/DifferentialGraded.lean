/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Endomorphism
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.Linear
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded

/-!
# Differential graded module sheaves over an algebra sheaf

This file owns the coefficient-linear complex category and its endomorphism DGA.  Constructions
such as enriched Hom and tensoring with a fixed complex can therefore share one low-level owner.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory
open scoped SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- Cochain complexes of module sheaves over a sheaf of commutative `R`-algebras.

This is a named type owner, rather than an `abbrev`, so the algebra sheaf and its coefficient
ring remain visible to typeclass search. -/
@[stacks 09LV "complexes of modules over an algebra sheaf"]
def Complex (O : Sheaf J (CommAlgCat.{w} R)) :=
  CochainComplex (SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) ℤ

/-- The ordinary category of complexes of module sheaves over `O`. -/
@[stacks 09LV "category of complexes over an algebra sheaf"]
noncomputable instance category (O : Sheaf J (CommAlgCat.{w} R)) : Category (Complex O) :=
  inferInstanceAs
    (Category (CochainComplex (SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) ℤ))

/-- The canonical integer shifts on complexes of module sheaves over `O`. -/
@[stacks 09LV "shifts of complexes over an algebra sheaf"]
noncomputable instance complexHasShift (O : Sheaf J (CommAlgCat.{w} R)) :
    HasShift (Complex O) ℤ :=
  inferInstanceAs
    (HasShift
      (CochainComplex (SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) ℤ) ℤ)

/-- The `R`-linear endomorphism DGA of a module-sheaf complex. -/
@[stacks 09LV "endomorphism DGA over the base ring"]
abbrev endDGA (K : Complex O) :=
  DifferentialGradedCategory.endomorphismDGA
    (D := CategoryTheory.CochainComplex.differentialGradedCategory
      (SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) R) K

/-- The canonical `R`-linear DG category structure on `Complex O`. -/
@[stacks 09LV "differential graded category of module-sheaf complexes", implicit_reducible]
noncomputable def complexDgCategory (O : Sheaf J (CommAlgCat.{w} R)) :
    DifferentialGradedCategory R (Complex O) :=
  CategoryTheory.CochainComplex.differentialGradedCategory
    (SheafOfModules.CommAlg.Modules.{r, u, v, w, z} O) R

/-- The canonical differential graded category on complexes of module sheaves.  Registering this
instance keeps DG-functor constructions inferable at every coefficient ring. -/
@[stacks 09LV "canonical DG category instance for algebra-sheaf complexes"]
noncomputable instance differentialGradedCategory (O : Sheaf J (CommAlgCat.{w} R)) :
    DifferentialGradedCategory R (Complex O) :=
  complexDgCategory O

#synth DifferentialGradedCategory R (Complex O)
#synth Category (Complex O)
#synth HasShift (Complex O) ℤ

end SheafOfModules.CommAlg
