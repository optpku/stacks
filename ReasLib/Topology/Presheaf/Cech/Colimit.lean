/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Ulift
public import ReasLib.Topology.Presheaf.Cech.Refinement
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Čech cohomology as an open-cover refinement colimit

The coefficient-valued refinement diagram is lifted by one universe before taking its colimit.
This keeps the universes of the ambient space, cover indices, and coefficients independent while
placing the refinement category inside the target universe.  Evaluation at a coefficient
presheaf recovers the corresponding fixed-coefficient colimit up to canonical isomorphism.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace TopCat.Presheaf.Cech.Colimit

variable {X : TopCat.{u}}

/-- The universe lift used before taking a colimit over indexed open covers. -/
@[stacks 09UZ "universe lift for open-cover Cech cohomology"]
abbrev universeLift.{s} : AddCommGrpCat.{s} ⥤ AddCommGrpCat.{s + 1} :=
  AddCommGrpCat.uliftFunctor.{s + 1, s}

/-- Postcomposition by `universeLift` on functors of the coefficient presheaf. -/
@[stacks 09UZ "coefficient lift for open-cover Cech cohomology"]
abbrev coefficientLift :
    (X.Presheaf AddCommGrpCat.{max u v w} ⥤ AddCommGrpCat.{max u v w}) ⥤
      (X.Presheaf AddCommGrpCat.{max u v w} ⥤
        AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}) :=
  (Functor.whiskeringRight
    (X.Presheaf AddCommGrpCat.{max u v w}) AddCommGrpCat.{max u v w}
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}).obj
      universeLift.{max u v w}

/-- The coefficient-valued Čech refinement diagram, lifted to a universe containing the
open-cover refinement category. -/
@[stacks 09UZ "lifted coefficient-valued open-cover refinement diagram"]
abbrev liftedDiagram (X : TopCat.{u}) (p : ℕ) :
    OpenCover.RefinementCategory.{v} X ⥤
      (X.Presheaf AddCommGrpCat.{max u v w} ⥤
        AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}) :=
  refinementDiagram.{w, v, u} X p ⋙ coefficientLift.{w, v, u} (X := X)

/-- Čech cohomology over all indexed open covers in degree `p`, functorially in additive
coefficient presheaves. -/
@[stacks 09UZ "open-cover Cech cohomology functor"]
noncomputable abbrev cohomologyFunctor (X : TopCat.{u}) (p : ℕ) :
    X.Presheaf AddCommGrpCat.{max u v w} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  colimit (liftedDiagram.{w, v, u} X p)

namespace cohomologyFunctor

/-- Evaluation at a coefficient presheaf commutes canonically with the open-cover refinement
colimit. -/
@[stacks 09UZ "evaluation of the open-cover Cech colimit"]
noncomputable def objIsoColimit
    (X : TopCat.{u}) (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    (cohomologyFunctor.{w, v, u} X p).obj F ≅
      colimit (refinementFunctor.{w, v, u} F p ⋙ universeLift.{max u v w}) :=
  colimitObjIsoColimitCompEvaluation (liftedDiagram.{w, v, u} X p) F

end cohomologyFunctor

/-- Čech cohomology over all indexed open covers with one fixed additive coefficient
presheaf. -/
@[stacks 09UZ "open-cover Cech cohomology with fixed coefficients"]
noncomputable abbrev cohomology
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (cohomologyFunctor.{w, v, u} X p).obj F

/-- The lifted coefficient functor at the refinement stage represented by an indexed open
cover. -/
@[stacks 09UZ "open-cover Cech refinement stage functor"]
abbrev stageFunctor (𝒰 : OpenCover.{v} X) (p : ℕ) :
    X.Presheaf AddCommGrpCat.{max u v w} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (liftedDiagram.{w, v, u} X p).obj 𝒰.refinementObject

/-- The lifted Čech cohomology object at the stage represented by an indexed open cover. -/
@[stacks 09UZ "open-cover Cech refinement stage cohomology"]
abbrev stageCohomology (𝒰 : OpenCover.{v} X)
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (stageFunctor.{w, v, u} 𝒰 p).obj F

/-- The canonical natural transformation from one open-cover refinement stage to the Čech
cohomology colimit. -/
@[stacks 09UZ "open-cover Cech refinement stage injection"]
noncomputable abbrev stageι (𝒰 : OpenCover.{v} X) (p : ℕ) :
    stageFunctor.{w, v, u} 𝒰 p ⟶ cohomologyFunctor.{w, v, u} X p :=
  colimit.ι (liftedDiagram.{w, v, u} X p) 𝒰.refinementObject

/-- The component of `stageι` at one additive coefficient presheaf. -/
@[stacks 09UZ "open-cover Cech refinement stage map"]
noncomputable abbrev stageMap (𝒰 : OpenCover.{v} X)
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    stageCohomology.{w, v, u} 𝒰 F p ⟶ cohomology.{w, v, u} F p :=
  (stageι.{w, v, u} 𝒰 p).app F

namespace cohomologyFunctor.objIsoColimit

/-- A stage map followed by the pointwise-colimit isomorphism is the corresponding colimit
injection. -/
@[reassoc (attr := simp), stacks 09UZ "open-cover stage map into the pointwise colimit"]
theorem stageMap_hom (𝒰 : OpenCover.{v} X)
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    stageMap.{w, v, u} 𝒰 F p ≫
        (cohomologyFunctor.objIsoColimit.{w, v, u} X F p).hom =
      colimit.ι (refinementFunctor.{w, v, u} F p ⋙ universeLift.{max u v w})
        𝒰.refinementObject := sorry

/-- A pointwise colimit injection followed by the inverse evaluation isomorphism is the
corresponding stage map. -/
@[reassoc (attr := simp), stacks 09UZ "pointwise colimit injection as an open-cover stage map"]
theorem ι_inv (𝒰 : OpenCover.{v} X)
    (F : X.Presheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    colimit.ι (refinementFunctor.{w, v, u} F p ⋙ universeLift.{max u v w})
        𝒰.refinementObject ≫
      (cohomologyFunctor.objIsoColimit.{w, v, u} X F p).inv =
        stageMap.{w, v, u} 𝒰 F p := sorry

end cohomologyFunctor.objIsoColimit

end TopCat.Presheaf.Cech.Colimit


