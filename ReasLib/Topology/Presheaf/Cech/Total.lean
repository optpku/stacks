/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Total
public import ReasLib.Topology.Presheaf.Cech.Basic

/-!
# Total Cech complexes of topological presheaves

This leaf specializes the coefficient-independent total Cech construction to additive-group-valued
presheaves on a topological space.  The coefficient universe is chosen large enough for both the
space and the cover index, so downstream tensor constructions see one stable presheaf category.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open ComplexShape HomologicalComplex HomologicalComplex₂

noncomputable section

universe u uι

namespace TopCat.Presheaf.Cech.Total

variable {X : TopCat.{u}} {ι : Type uι}

/-- The integer-indexed Cech row functor of an indexed family of opens. -/
@[stacks 07MB "topological row Cech infrastructure for total cup-product constructions"]
abbrev rowCechFunctor (U : ι → Opens X) :
    X.Presheaf AddCommGrpCat.{max u uι} ⥤ CochainComplex AddCommGrpCat.{max u uι} ℤ :=
  CategoryTheory.Cech.Total.rowCechFunctor
    (C := Opens X) (A := AddCommGrpCat.{max u uι}) U

/-- Transfer canonical Cech additivity through extension by zero.  The explicit coefficient
universe makes this composition available to the topological row interface. -/
instance rowCechFunctor_additive (U : ι → Opens X) : (rowCechFunctor U).Additive := by
  change (CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{max u uι}) U ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u uι}).Additive
  letI := CategoryTheory.Cech.cechComplexFunctor_additive
    (A := AddCommGrpCat.{max u uι}) U
  infer_instance

/-- The rowwise Cech double-complex functor of an indexed family of opens. -/
@[stacks 07MB "topological double Cech infrastructure for total cup-product constructions"]
abbrev doubleCechFunctor (U : ι → Opens X) :
    CochainComplex (X.Presheaf AddCommGrpCat.{max u uι}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u uι} (up ℤ) (up ℤ) :=
  CategoryTheory.Cech.Total.doubleCechFunctor
    (C := Opens X) (A := AddCommGrpCat.{max u uι}) U

/-- The total Cech complex functor of an indexed family of opens. -/
@[stacks 07MB "topological total Cech infrastructure for total cup-product constructions"]
abbrev totalCechFunctor (U : ι → Opens X) :
    CochainComplex (X.Presheaf AddCommGrpCat.{max u uι}) ℤ ⥤
      CochainComplex AddCommGrpCat.{max u uι} ℤ :=
  CategoryTheory.Cech.Total.totalCechFunctor
    (C := Opens X) (A := AddCommGrpCat.{max u uι}) U

end TopCat.Presheaf.Cech.Total

end
