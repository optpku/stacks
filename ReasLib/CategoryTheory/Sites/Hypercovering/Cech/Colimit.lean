module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Refinement
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Colimit

/-!
# Hypercovering Cech cohomology as a refinement colimit

The refinement diagram is lifted by one universe before taking its pointwise colimit.  This
reflects the smallness bound for the collection of hypercoverings and keeps the colimit itself
canonical, rather than asking downstream users to supply a colimit presentation.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits

namespace Hypercovering.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C]

section Cohomology

variable [HasWeakSheafify J AddCommGrpCat.{max w v}]

/-- The refinement diagram of Cech cohomology functors, lifted to a universe containing its
small indexing category. -/
abbrev liftedDiagram (X : C) (i : ℕ) :
    Hypercovering.RefinementCategory.{w} J X ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤
        AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}) :=
  Hypercovering.RefinementCategory.toPresheafTarget (J := J) (X := X) ⋙
    HypercoveringOf.Cech.liftedDiagram (J := J) (uliftYoneda.{w}.obj X) i

/-- Section 25.10 (Tag 01GZ): hypercovering Cech cohomology in degree `i`, functorially in the
coefficient sheaf, is the colimit of the lifted refinement diagram. -/
@[stacks 01GZ "hypercovering Cech cohomology functor"]
noncomputable abbrev cohomologyFunctor (X : C) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  colimit (liftedDiagram X i)

namespace cohomologyFunctor

/-- Evaluation at a coefficient sheaf commutes canonically with the fixed-target refinement
colimit. -/
@[stacks 01GZ "evaluation of the fixed-target hypercovering colimit"]
noncomputable def objIsoColimit
    (X : C) (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    (cohomologyFunctor X i).obj I ≅
      colimit (refinementFunctor (J := J) X I i ⋙
        HypercoveringOf.Cech.universeLift.{max u v w}) :=
  colimitObjIsoColimitCompEvaluation (liftedDiagram X i) I

end cohomologyFunctor

/-- Fixed-target hypercovering Cech cohomology with one coefficient sheaf. -/
noncomputable abbrev colimitCohomology (X : C)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (cohomologyFunctor X i).obj I

/-- The lifted Cech cohomology functor at the refinement stage represented by `K`. -/
abbrev stageFunctor {X : C} (K : Hypercovering.{w} J X) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (liftedDiagram X i).obj K.refinementObject

/-- The lifted Cech cohomology group at the refinement stage represented by `K`. -/
abbrev stageCohomology {X : C} (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (stageFunctor K i).obj I

/-- The canonical natural transformation from one fixed-target refinement stage to
hypercovering Cech cohomology. -/
@[stacks 01GZ "fixed-target refinement stage injection"]
noncomputable abbrev stageι {X : C} (K : Hypercovering.{w} J X) (i : ℕ) :
    stageFunctor K i ⟶ cohomologyFunctor X i :=
  colimit.ι (liftedDiagram X i) K.refinementObject

/-- The component of `stageι` at one coefficient sheaf. -/
noncomputable abbrev stageMap {X : C} (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    stageCohomology K I i ⟶ colimitCohomology X I i :=
  (stageι K i).app I

namespace cohomologyFunctor.objIsoColimit

/-- A fixed-target stage map followed by the pointwise-colimit isomorphism is the corresponding
colimit injection. -/
@[reassoc (attr := simp)]
theorem stageMap_hom {X : C} (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    stageMap K I i ≫ (cohomologyFunctor.objIsoColimit X I i).hom =
      colimit.ι (refinementFunctor (J := J) X I i ⋙
        HypercoveringOf.Cech.universeLift.{max u v w}) K.refinementObject := sorry

/-- A fixed-target pointwise colimit injection followed by the inverse is the corresponding
stage map. -/
@[reassoc (attr := simp)]
theorem ι_inv {X : C} (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    colimit.ι (refinementFunctor (J := J) X I i ⋙
        HypercoveringOf.Cech.universeLift.{max u v w}) K.refinementObject ≫
      (cohomologyFunctor.objIsoColimit X I i).inv = stageMap K I i := sorry

end cohomologyFunctor.objIsoColimit

end Cohomology

end Hypercovering.Cech

end CategoryTheory
