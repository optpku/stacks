module

public import ReasLib.CategoryTheory.Sites.Cech.Additive
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total complexes of Cech complexes

@stack 07MB

This leaf owns the coefficient-independent row, double-complex, and total-complex composites
used by Cech comparison maps.  Product or Alexander--Whitney structure is deliberately kept in
separate leaves: these functors only package the canonical total-complex construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex HomologicalComplex₂

noncomputable section

universe w vA uA v u

namespace CategoryTheory.Cech.Total

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts A]
variable [HasZeroObject A] [HasCoproducts A]
variable {ι : Type w}

/-- The integer-indexed row Cech functor obtained by extending the ordinary Cech complex by zero.
-/
@[stacks 07MB "row Cech infrastructure for total cup-product constructions"]
abbrev rowCechFunctor (U : ι → C) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℤ :=
  cechComplexFunctor U ⋙ ComplexShape.embeddingUpNat.extendFunctor A

/-- The rowwise Cech double-complex functor on integer-indexed presheaf complexes. -/
@[stacks 07MB "double Cech infrastructure for total cup-product constructions"]
abbrev doubleCechFunctor (U : ι → C) :
    CochainComplex (Cᵒᵖ ⥤ A) ℤ ⥤ HomologicalComplex₂ A (up ℤ) (up ℤ) :=
  (rowCechFunctor (A := A) U).mapHomologicalComplex (up ℤ)

/-- The total Cech complex functor obtained from the canonical double-complex totalization.
-/
@[stacks 07MB "total Cech-complex infrastructure"]
abbrev totalCechFunctor (U : ι → C) :
    CochainComplex (Cᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  doubleCechFunctor (A := A) U ⋙
    (HomologicalComplex₂.totalFunctor A (up ℤ) (up ℤ) (up ℤ) :
      HomologicalComplex₂ A (up ℤ) (up ℤ) ⥤ HomologicalComplex A (up ℤ))

end CategoryTheory.Cech.Total

end
