module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
public import stacks_project.Chap07.Definition_7_20_1_Cocontinuous
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf
public import stacks_project.Chap103.Definition_103_14_1_Sites

/-!
# Continuity of lisse-étale and flat-fppf inclusions

The inclusions of the lisse-étale and flat-fppf sites of an algebraic stack into
the associated étale site and the inherited fppf site are continuous and
cocontinuous, at both the Grothendieck-topology and selected-precoverage layers.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The lisse-étale inclusion is continuous for the lisse-étale topology and the
associated étale topology. -/
instance lisseEtaleInclusion.instIsContinuous (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInclusion X).IsContinuous (lisseEtaleTopology X) X.etaleTopology :=
  sorry

/-- The lisse-étale inclusion is cocontinuous for the lisse-étale topology and the
associated étale topology. -/
instance lisseEtaleInclusion.instIsCocontinuous (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInclusion X).IsCocontinuous (lisseEtaleTopology X) X.etaleTopology :=
  sorry

/-- The flat-fppf inclusion is continuous into the inherited fppf topology. -/
instance flatFppfInclusion.instIsContinuous (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInclusion X).IsContinuous (flatFppfTopology X) (inheritedFppfTopology X) :=
  sorry

/-- The flat-fppf inclusion is cocontinuous into the inherited fppf topology. -/
instance flatFppfInclusion.instIsCocontinuous (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInclusion X).IsCocontinuous (flatFppfTopology X) (inheritedFppfTopology X) :=
  sorry

/-- The lisse-étale inclusion preserves selected covering families of the
lisse-étale precoverage. -/
instance lisseEtaleInclusion.instPrecoverageIsContinuous
    (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.Precoverage.IsContinuous (lisseEtaleInclusion X)
      (lisseEtalePrecoverage X) X.etaleTopology.toPrecoverage :=
  sorry

/-- The lisse-étale inclusion is cocontinuous for selected covering families. -/
instance lisseEtaleInclusion.instPrecoverageIsCocontinuous
    (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.Precoverage.IsCocontinuous (lisseEtaleInclusion X)
      (lisseEtalePrecoverage X) X.etaleTopology.toPrecoverage :=
  sorry

/-- The flat-fppf inclusion preserves selected covering families of the
flat-fppf precoverage. -/
instance flatFppfInclusion.instPrecoverageIsContinuous
    (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.Precoverage.IsContinuous (flatFppfInclusion X)
      (flatFppfPrecoverage X) (inheritedFppfTopology X).toPrecoverage :=
  sorry

/-- The flat-fppf inclusion is cocontinuous for selected covering families. -/
instance flatFppfInclusion.instPrecoverageIsCocontinuous
    (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.Precoverage.IsCocontinuous (flatFppfInclusion X)
      (flatFppfPrecoverage X) (inheritedFppfTopology X).toPrecoverage :=
  sorry

/-- Type-valued sheafification exists on the lisse-étale site. -/
instance lisseEtaleTopology_hasSheafify_type (X : GroupoidsOver S) [AlgebraicStack X] :
    HasSheafify (lisseEtaleTopology X) (Type u) := sorry

/-- Type-valued sheafification exists on the associated étale site. -/
instance etaleTopology_hasSheafify_type (X : GroupoidsOver S) :
    HasSheafify X.etaleTopology (Type u) := sorry

/-- Type-valued sheafification exists on the flat-fppf site. -/
instance flatFppfTopology_hasSheafify_type (X : GroupoidsOver S) [AlgebraicStack X] :
    HasSheafify (flatFppfTopology X) (Type u) := sorry

/-- Type-valued sheafification exists on the inherited fppf site. -/
instance inheritedFppfTopology_hasSheafify_type (X : GroupoidsOver S) :
    HasSheafify (inheritedFppfTopology X) (Type u) := sorry

/-- Abelian sheafification exists on the lisse-étale site. -/
instance lisseEtaleTopology_hasSheafify_addCommGrp (X : GroupoidsOver S) [AlgebraicStack X] :
    HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u} := sorry

/-- Abelian sheafification exists on the associated étale site. -/
instance etaleTopology_hasSheafify_addCommGrp (X : GroupoidsOver S) :
    HasSheafify X.etaleTopology AddCommGrpCat.{u} := sorry

/-- Abelian sheafification exists on the flat-fppf site. -/
instance flatFppfTopology_hasSheafify_addCommGrp (X : GroupoidsOver S) [AlgebraicStack X] :
    HasSheafify (flatFppfTopology X) AddCommGrpCat.{u} := sorry

/-- Abelian sheafification exists on the inherited fppf site. -/
instance inheritedFppfTopology_hasSheafify_addCommGrp (X : GroupoidsOver S) :
    HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u} := sorry

/-- Ring-valued sheaves on the lisse-étale topology compose with `forget RingCat`. -/
instance lisseEtaleTopology_hasSheafCompose (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u}) := sorry

/-- Ring-valued sheaves on the associated étale topology compose with `forget RingCat`. -/
instance etaleTopology_hasSheafCompose (X : GroupoidsOver S) :
    X.etaleTopology.HasSheafCompose (forget RingCat.{u}) := sorry

/-- Ring-valued sheaves on the flat-fppf topology compose with `forget RingCat`. -/
instance flatFppfTopology_hasSheafCompose (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfTopology X).HasSheafCompose (forget RingCat.{u}) := sorry

/-- Ring-valued sheaves on the inherited fppf topology compose with `forget RingCat`. -/
instance inheritedFppfTopology_hasSheafCompose (X : GroupoidsOver S) :
    (inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u}) := sorry

/-- Pointwise right Kan extensions of type-valued presheaves along the lisse-étale
inclusion. -/
instance lisseEtaleInclusion.op_hasPointwiseRightKanExtension_type
    (X : GroupoidsOver S) [AlgebraicStack X] (P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u) :
    (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P := sorry

/-- Left Kan extensions of type-valued presheaves along the lisse-étale inclusion. -/
instance lisseEtaleInclusion.op_hasLeftKanExtension_type
    (X : GroupoidsOver S) [AlgebraicStack X] (P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u) :
    (lisseEtaleInclusion X).op.HasLeftKanExtension P := sorry

/-- Pointwise left Kan extensions of type-valued presheaves along the lisse-étale
inclusion. -/
instance lisseEtaleInclusion.op_hasPointwiseLeftKanExtension_type
    (X : GroupoidsOver S) [AlgebraicStack X] (P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u) :
    (lisseEtaleInclusion X).op.HasPointwiseLeftKanExtension P := sorry

/-- Pointwise right Kan extensions of abelian presheaves along the lisse-étale
inclusion. -/
instance lisseEtaleInclusion.op_hasPointwiseRightKanExtension_addCommGrp
    (X : GroupoidsOver S) [AlgebraicStack X]
    (P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (lisseEtaleInclusion X).op.HasPointwiseRightKanExtension P := sorry

/-- Left Kan extensions of abelian presheaves along the lisse-étale inclusion. -/
instance lisseEtaleInclusion.op_hasLeftKanExtension_addCommGrp
    (X : GroupoidsOver S) [AlgebraicStack X]
    (P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (lisseEtaleInclusion X).op.HasLeftKanExtension P := sorry

/-- Pointwise left Kan extensions of abelian presheaves along the lisse-étale
inclusion. -/
instance lisseEtaleInclusion.op_hasPointwiseLeftKanExtension_addCommGrp
    (X : GroupoidsOver S) [AlgebraicStack X]
    (P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (lisseEtaleInclusion X).op.HasPointwiseLeftKanExtension P := sorry

/-- Pointwise right Kan extensions of type-valued presheaves along the flat-fppf
inclusion. -/
instance flatFppfInclusion.op_hasPointwiseRightKanExtension_type
    (X : GroupoidsOver S) [AlgebraicStack X] (P : (flatFppfSite X)ᵒᵖ ⥤ Type u) :
    (flatFppfInclusion X).op.HasPointwiseRightKanExtension P := sorry

/-- Left Kan extensions of type-valued presheaves along the flat-fppf inclusion. -/
instance flatFppfInclusion.op_hasLeftKanExtension_type
    (X : GroupoidsOver S) [AlgebraicStack X] (P : (flatFppfSite X)ᵒᵖ ⥤ Type u) :
    (flatFppfInclusion X).op.HasLeftKanExtension P := sorry

/-- Pointwise left Kan extensions of type-valued presheaves along the flat-fppf
inclusion. -/
instance flatFppfInclusion.op_hasPointwiseLeftKanExtension_type
    (X : GroupoidsOver S) [AlgebraicStack X] (P : (flatFppfSite X)ᵒᵖ ⥤ Type u) :
    (flatFppfInclusion X).op.HasPointwiseLeftKanExtension P := sorry

/-- Pointwise right Kan extensions of abelian presheaves along the flat-fppf
inclusion. -/
instance flatFppfInclusion.op_hasPointwiseRightKanExtension_addCommGrp
    (X : GroupoidsOver S) [AlgebraicStack X]
    (P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (flatFppfInclusion X).op.HasPointwiseRightKanExtension P := sorry

/-- Left Kan extensions of abelian presheaves along the flat-fppf inclusion. -/
instance flatFppfInclusion.op_hasLeftKanExtension_addCommGrp
    (X : GroupoidsOver S) [AlgebraicStack X]
    (P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (flatFppfInclusion X).op.HasLeftKanExtension P := sorry

/-- Pointwise left Kan extensions of abelian presheaves along the flat-fppf
inclusion. -/
instance flatFppfInclusion.op_hasPointwiseLeftKanExtension_addCommGrp
    (X : GroupoidsOver S) [AlgebraicStack X]
    (P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (flatFppfInclusion X).op.HasPointwiseLeftKanExtension P := sorry

end AlgebraicGeometry.AlgebraicStack
