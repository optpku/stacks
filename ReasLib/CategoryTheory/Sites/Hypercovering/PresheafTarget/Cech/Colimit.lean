/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Ulift
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Refinement
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presheaf-target hypercovering Cech cohomology as a refinement colimit

The canonical colimit is formed once in the category of coefficient-valued functors. Evaluation
at a coefficient sheaf then recovers the corresponding fixed-coefficient colimit up to canonical
isomorphism. Comparison maps out of this colimit live in the separate `ColimitComparison` leaf.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.HypercoveringOf.Cech

open Limits

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {G : Cᵒᵖ ⥤ Type (max w v)}

/-- The universe lift used before taking a colimit over presheaf-target hypercoverings. -/
abbrev universeLift.{s} : AddCommGrpCat.{s} ⥤ AddCommGrpCat.{s + 1} :=
  AddCommGrpCat.uliftFunctor.{s + 1, s}

/-- Postcomposition with the universe lift for functors of the coefficient sheaf. -/
abbrev coefficientLift :
    (Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w}) ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤
        AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}) :=
  (Functor.whiskeringRight
    (Sheaf J AddCommGrpCat.{max w v}) AddCommGrpCat.{max u v w}
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}).obj universeLift.{max u v w}

section Cohomology

variable [HasWeakSheafify J AddCommGrpCat.{max w v}]

/-- The coefficient-valued Cech refinement diagram, lifted to a universe containing its index
category. -/
@[stacks 09VZ "lifted coefficient-valued refinement diagram"]
abbrev liftedDiagram (G : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :
    HypercoveringOf.RefinementCategory J G ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤
        AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}) :=
  refinementDiagram G i ⋙ coefficientLift (J := J)

/-- Presheaf-target hypercovering Cech cohomology in degree `i`, functorially in the coefficient
sheaf. -/
@[stacks 09VZ "presheaf-target hypercovering Cech cohomology functor"]
noncomputable abbrev cohomologyFunctor (G : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  colimit (liftedDiagram G i)

namespace cohomologyFunctor

/-- Evaluation at a coefficient sheaf commutes canonically with the refinement colimit. -/
@[stacks 09VZ "evaluation of the hypercovering colimit"]
noncomputable def objIsoColimit
    (G : Cᵒᵖ ⥤ Type (max w v))
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    (cohomologyFunctor G i).obj I ≅
      colimit (refinementFunctor G I i ⋙ universeLift.{max u v w}) :=
  colimitObjIsoColimitCompEvaluation (liftedDiagram G i) I

end cohomologyFunctor

/-- Presheaf-target hypercovering Cech cohomology with one fixed coefficient sheaf. -/
noncomputable abbrev colimitCohomology (G : Cᵒᵖ ⥤ Type (max w v))
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (cohomologyFunctor G i).obj I

/-- The lifted Cech cohomology functor at the refinement stage represented by `K`. -/
abbrev stageFunctor (K : HypercoveringOf J G) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (liftedDiagram G i).obj (HypercoveringOf.refinementObject K)

/-- The lifted Cech cohomology group at the stage represented by `K`. -/
abbrev stageCohomology (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (stageFunctor K i).obj I

/-- The canonical natural transformation from one refinement stage to the hypercovering Cech
cohomology functor. -/
@[stacks 09VZ "refinement stage injection"]
noncomputable abbrev stageι (K : HypercoveringOf J G) (i : ℕ) :
    stageFunctor K i ⟶ cohomologyFunctor G i :=
  colimit.ι (liftedDiagram G i) (HypercoveringOf.refinementObject K)

/-- The component of `stageι` at a fixed coefficient sheaf. -/
noncomputable abbrev stageMap (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    stageCohomology K I i ⟶ colimitCohomology G I i :=
  (stageι K i).app I

namespace cohomologyFunctor.objIsoColimit

/-- A stage map followed by the pointwise-colimit isomorphism is the corresponding colimit
injection. -/
@[reassoc (attr := simp)]
theorem stageMap_hom (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    stageMap K I i ≫ (cohomologyFunctor.objIsoColimit G I i).hom =
      colimit.ι (refinementFunctor G I i ⋙ universeLift.{max u v w})
        (HypercoveringOf.refinementObject K) := sorry

/-- A pointwise colimit injection followed by the inverse is the corresponding stage map. -/
@[reassoc (attr := simp)]
theorem ι_inv (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    colimit.ι (refinementFunctor G I i ⋙ universeLift.{max u v w})
        (HypercoveringOf.refinementObject K) ≫
      (cohomologyFunctor.objIsoColimit G I i).inv = stageMap K I i := sorry

end cohomologyFunctor.objIsoColimit

end Cohomology

end CategoryTheory.HypercoveringOf.Cech
