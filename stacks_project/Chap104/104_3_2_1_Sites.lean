/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf
public import stacks_project.Chap103.Definition_103_14_1_Sites
public import stacks_project.Chap103.«103_15_1_1_Map»

/-!
# Continuity of lisse-étale and flat-fppf inclusions

The inclusions `g` and `g'` of the lisse-étale (resp. flat-fppf) site into the
associated étale site (resp. the inherited fppf site carrying `𝒪`) are
continuous and cocontinuous. Restricted site functors of smooth or flat
1-morphisms are `lisseEtaleMap` and `flatFppfMap` from Chap103.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver
open CategoryTheory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

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

end AlgebraicGeometry.AlgebraicStack
