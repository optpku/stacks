/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Presheaf.Cech.Colimit
public import ReasLib.Topology.Sheaf.Cohomology.Bridge
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison from global Cech cohomology to sheaf cohomology

The open-cover refinement diagram is first restricted from additive presheaves to additive
sheaves. A refinement-natural family of coverwise comparison maps then gives a concrete cocone,
and hence a comparison from the refinement colimit to global sheaf cohomology.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace TopCat.Sheaf.Cohomology.Cech

variable {X : TopCat.{u}}

/-- The open-cover refinement diagram of Cech cohomology, restricted from additive presheaves
to additive sheaves. -/
@[stacks 09UZ "sheaf-coefficient open-cover refinement diagram"]
abbrev refinementDiagram (X : TopCat.{u}) (p : ℕ) :
    OpenCover.RefinementCategory.{v} X ⥤
      (X.Sheaf AddCommGrpCat.{max u v w} ⥤
        AddCommGrpCat.{max u v w}) :=
  TopCat.Presheaf.Cech.refinementDiagram.{w, v, u} X p ⋙
    (Functor.whiskeringLeft
      (X.Sheaf AddCommGrpCat.{max u v w})
      (X.Presheaf AddCommGrpCat.{max u v w})
      AddCommGrpCat.{max u v w}).obj
      (TopCat.Sheaf.forget AddCommGrpCat.{max u v w} X)

/-- Postcomposition by the canonical universe lift for functors of an additive sheaf. -/
@[stacks 09UZ "sheaf coefficient lift for open-cover Cech cohomology"]
abbrev coefficientLift (X : TopCat.{u}) :
    (X.Sheaf AddCommGrpCat.{max u v w} ⥤
      AddCommGrpCat.{max u v w}) ⥤
      (X.Sheaf AddCommGrpCat.{max u v w} ⥤
        AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}) :=
  (Functor.whiskeringRight
    (X.Sheaf AddCommGrpCat.{max u v w})
    AddCommGrpCat.{max u v w}
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}).obj
      TopCat.Presheaf.Cech.Colimit.universeLift.{max u v w}

/-- The sheaf-restricted open-cover refinement diagram, lifted to a universe containing its
index category. -/
@[stacks 09UZ "lifted sheaf-coefficient open-cover refinement diagram"]
abbrev liftedDiagram (X : TopCat.{u}) (p : ℕ) :
    OpenCover.RefinementCategory.{v} X ⥤
      (X.Sheaf AddCommGrpCat.{max u v w} ⥤
        AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}) :=
  TopCat.Presheaf.Cech.Colimit.liftedDiagram.{w, v, u} X p ⋙
    (Functor.whiskeringLeft
      (X.Sheaf AddCommGrpCat.{max u v w})
      (X.Presheaf AddCommGrpCat.{max u v w})
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}).obj
      (TopCat.Sheaf.forget AddCommGrpCat.{max u v w} X)

/-- Global Cech cohomology as the colimit of the sheaf-restricted lifted refinement diagram. -/
@[stacks 09UZ "global Cech cohomology functor"]
noncomputable abbrev cohomologyFunctor (X : TopCat.{u}) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{max u v w} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  colimit (liftedDiagram.{w, v, u} X p)

/-- Restricting the presheaf-coefficient Cech colimit to sheaves agrees canonically with taking
the colimit after restriction. -/
@[stacks 09UZ "restriction of the open-cover Cech cohomology functor to sheaves"]
noncomputable def cohomologyFunctorIso (X : TopCat.{u}) (p : ℕ) :
    cohomologyFunctor.{w, v, u} X p ≅
      TopCat.Sheaf.forget AddCommGrpCat.{max u v w} X ⋙
        TopCat.Presheaf.Cech.Colimit.cohomologyFunctor.{w, v, u} X p :=
  colimitCompWhiskeringLeftIsoCompColimit
    (TopCat.Presheaf.Cech.Colimit.liftedDiagram.{w, v, u} X p)
    (TopCat.Sheaf.forget AddCommGrpCat.{max u v w} X)

/-- Global Cech cohomology with one fixed coefficient sheaf. -/
@[stacks 09UZ "open-cover Cech cohomology with fixed sheaf coefficients"]
noncomputable abbrev cohomology
    (F : X.Sheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (cohomologyFunctor.{w, v, u} X p).obj F

/-- The lifted coverwise Cech cohomology functor at the refinement stage represented by
`U`. -/
@[stacks 09UZ "open-cover Cech refinement stage functor on sheaves"]
abbrev stageFunctor (U : OpenCover.{v} X) (p : ℕ) :
    X.Sheaf AddCommGrpCat.{max u v w} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (liftedDiagram.{w, v, u} X p).obj U.refinementObject

/-- The lifted coverwise Cech cohomology group at `U` with one fixed coefficient sheaf. -/
@[stacks 09UZ "open-cover Cech refinement stage cohomology with sheaf coefficients"]
abbrev stageCohomology (U : OpenCover.{v} X)
    (F : X.Sheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (stageFunctor.{w, v, u} U p).obj F

/-- The canonical natural transformation from one represented cover stage to global Cech
cohomology. -/
@[stacks 09UZ "open-cover Cech refinement stage injection on sheaves"]
noncomputable abbrev stageι (U : OpenCover.{v} X) (p : ℕ) :
    stageFunctor.{w, v, u} U p ⟶ cohomologyFunctor.{w, v, u} X p :=
  colimit.ι (liftedDiagram.{w, v, u} X p) U.refinementObject

/-- The component of the cover-stage injection at one fixed coefficient sheaf. -/
@[stacks 09UZ "open-cover Cech refinement stage map with sheaf coefficients"]
noncomputable abbrev stageMap (U : OpenCover.{v} X)
    (F : X.Sheaf AddCommGrpCat.{max u v w}) (p : ℕ) :
    stageCohomology.{w, v, u} U F p ⟶ cohomology.{w, v, u} F p :=
  (stageι.{w, v, u} U p).app F

namespace cohomologyFunctorIso

/-- The canonical restriction-colimit isomorphism carries every sheaf-valued stage injection
to the restriction of the corresponding presheaf-valued stage injection. -/
@[reassoc (attr := simp), stacks 09UZ "restriction-colimit isomorphism on Cech stage injections"]
theorem stageι_hom (U : OpenCover.{v} X) (p : ℕ) :
    stageι.{w, v, u} U p ≫ (cohomologyFunctorIso.{w, v, u} X p).hom =
      Functor.whiskerLeft (TopCat.Sheaf.forget AddCommGrpCat.{max u v w} X)
        (TopCat.Presheaf.Cech.Colimit.stageι.{w, v, u} U p) := sorry

end cohomologyFunctorIso

section Target

variable (X : TopCat.{u})
variable
  [h_sheafify : HasSheafify (Opens.grothendieckTopology X)
    AddCommGrpCat.{max u v w}]
  [h_ext : HasExt.{max u v w}
    (X.Sheaf AddCommGrpCat.{max u v w})]

/-- Global sheaf cohomology in degree `p`, functorially in the coefficient sheaf. -/
@[stacks 09UZ "global sheaf cohomology target for the Cech comparison"]
abbrev targetCohomology (p : ℕ) :
    X.Sheaf AddCommGrpCat.{max u v w} ⥤
      AddCommGrpCat.{max u v w} :=
  @CategoryTheory.Sheaf.functorH.{max u v w, max u v w, u, u}
    (Opens X) (inferInstanceAs (Category.{u} (Opens X)))
    (Opens.grothendieckTopology X)
    h_sheafify h_ext p

/-- Global sheaf cohomology lifted to the universe of the open-cover refinement colimit. -/
@[stacks 09UZ "universe-lifted sheaf cohomology target for the Cech comparison"]
abbrev liftedTargetCohomology (p : ℕ) :
    X.Sheaf AddCommGrpCat.{max u v w} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  targetCohomology.{w, v, u} X p ⋙
    TopCat.Presheaf.Cech.Colimit.universeLift.{max u v w}

/-- The constant refinement diagram with value global sheaf cohomology. -/
@[stacks 09UZ "constant sheaf cohomology target on open-cover refinements"]
abbrev refinementComparisonTarget (p : ℕ) :
    OpenCover.RefinementCategory.{v} X ⥤
      (X.Sheaf AddCommGrpCat.{max u v w} ⥤
        AddCommGrpCat.{max u v w}) :=
  (Functor.const (OpenCover.RefinementCategory.{v} X)).obj
    (targetCohomology.{w, v, u} X p)

/-- The constant lifted refinement diagram with value global sheaf cohomology. -/
@[stacks 09UZ "constant lifted sheaf cohomology target on open-cover refinements"]
abbrev liftedComparisonTarget (p : ℕ) :
    OpenCover.RefinementCategory.{v} X ⥤
      (X.Sheaf AddCommGrpCat.{max u v w} ⥤
        AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}) :=
  (Functor.const (OpenCover.RefinementCategory.{v} X)).obj
    (liftedTargetCohomology.{w, v, u} X p)

/-- A coverwise Cech-to-sheaf-cohomology comparison, natural in refinement classes and
coefficient sheaves. -/
@[stacks 09UZ "refinement-natural Cech-to-sheaf-cohomology comparison datum"]
abbrev RefinementComparison (p : ℕ) :=
  refinementDiagram.{w, v, u} X p ⟶
    refinementComparisonTarget.{w, v, u} X p

end Target

section Comparison

variable
  [h_sheafify : HasSheafify (Opens.grothendieckTopology X)
    AddCommGrpCat.{max u v w}]
  [h_ext : HasExt.{max u v w}
    (X.Sheaf AddCommGrpCat.{max u v w})]

/-- The lifted legs of a refinement-natural comparison satisfy the cocone equations. -/
@[stacks 09UZ "lifted Cech comparison cocone equations"]
theorem comparisonCocone_naturality {p : ℕ}
    (c : RefinementComparison.{w, v, u} X p)
    {K L : OpenCover.RefinementCategory.{v} X} (f : K ⟶ L) :
    (liftedDiagram.{w, v, u} X p).map f ≫
        (coefficientLift.{w, v, u} X).map (c.app L) =
      (coefficientLift.{w, v, u} X).map (c.app K) ≫
        (liftedComparisonTarget.{w, v, u} X p).map f := sorry

/-- The concrete cocone from coverwise Cech cohomology functors to lifted global sheaf
cohomology. -/
@[stacks 09UZ "Cech-to-sheaf-cohomology comparison cocone"]
noncomputable def comparisonCocone {p : ℕ}
    (c : RefinementComparison.{w, v, u} X p) :
    Cocone (liftedDiagram.{w, v, u} X p) where
  pt := liftedTargetCohomology.{w, v, u} X p
  ι :=
    { app K := (coefficientLift.{w, v, u} X).map (c.app K)
      naturality _ _ f := comparisonCocone_naturality.{w, v, u} c f }

/-- A refinement-natural stage comparison descends to the global Cech refinement colimit. -/
@[stacks 09UZ "global Cech-to-sheaf-cohomology comparison"]
noncomputable def comparison {p : ℕ}
    (c : RefinementComparison.{w, v, u} X p) :
    cohomologyFunctor.{w, v, u} X p ⟶
      liftedTargetCohomology.{w, v, u} X p :=
  colimit.desc (liftedDiagram.{w, v, u} X p)
    (comparisonCocone.{w, v, u} c)

namespace RefinementComparison

/-- The component of a refinement-natural comparison at an indexed open cover and a
coefficient sheaf. -/
abbrev stageMap {p : ℕ} (c : RefinementComparison.{w, v, u} X p)
    (U : OpenCover.{v} X) (F : X.Sheaf AddCommGrpCat.{max u v w}) :=
  (c.app U.refinementObject).app F

/-- A refinement comparison is jointly surjective when every target cohomology class is
represented at some open-cover stage. -/
@[stacks 09UZ "joint surjectivity of open-cover Cech comparison stages"]
def IsJointlySurjective {p : ℕ}
    (c : RefinementComparison.{w, v, u} X p) : Prop :=
  ∀ (F : X.Sheaf AddCommGrpCat.{max u v w})
    (y : (targetCohomology.{w, v, u} X p).obj F),
    ∃ (U : OpenCover.{v} X)
      (x : ((refinementDiagram.{w, v, u} X p).obj U.refinementObject).obj F),
      c.stageMap U F x = y

/-- A refinement comparison is eventually injective when a cover-stage class mapping to zero
already vanishes after passing to a further refinement. -/
@[stacks 09UZ "eventual injectivity of open-cover Cech comparison stages"]
def IsEventuallyInjective {p : ℕ}
    (c : RefinementComparison.{w, v, u} X p) : Prop :=
  ∀ (U : OpenCover.{v} X) (F : X.Sheaf AddCommGrpCat.{max u v w})
    (x : ((refinementDiagram.{w, v, u} X p).obj U.refinementObject).obj F),
    c.stageMap U F x = 0 →
      ∃ (V : OpenCover.{v} X) (r : U.Refinement V),
        (((refinementDiagram.{w, v, u} X p).map
          (OpenCover.refinementMap r)).app F) x = 0

/-- The elementwise filtered-colimit criterion for a refinement comparison to induce an
isomorphism: target classes occur at finite stages, and kernel classes eventually vanish. -/
@[stacks 09UZ "open-cover Cech colimit comparison criterion"]
def IsColimitIso {p : ℕ} (c : RefinementComparison.{w, v, u} X p) : Prop :=
  c.IsEventuallyInjective ∧ c.IsJointlySurjective

/-- The eventual-injectivity clause of the colimit comparison criterion. -/
theorem IsColimitIso.eventuallyInjective {p : ℕ}
    {c : RefinementComparison.{w, v, u} X p} (h : c.IsColimitIso) :
    c.IsEventuallyInjective := sorry

/-- The joint-surjectivity clause of the colimit comparison criterion. -/
theorem IsColimitIso.jointlySurjective {p : ℕ}
    {c : RefinementComparison.{w, v, u} X p} (h : c.IsColimitIso) :
    c.IsJointlySurjective := sorry

end RefinementComparison

/-- A refinement-natural Cech comparison is certified when its induced map out of the global
refinement colimit is invertible.  The raw `RefinementComparison` remains useful for comparison
maps which are not known to be isomorphisms, while this predicate is the reusable gate for a
canonical global comparison. -/
@[stacks 09UZ "certified open-cover Cech comparison"]
def IsCertified {p : ℕ} (c : RefinementComparison.{w, v, u} X p) : Prop :=
  IsIso (comparison c)

/-- The filtered-colimit criterion certifies the induced global comparison map. -/
@[stacks 09UZ "open-cover Cech colimit criterion certifies the comparison"]
theorem RefinementComparison.IsColimitIso.isCertified {p : ℕ}
    {c : RefinementComparison.{w, v, u} X p} (h : c.IsColimitIso) :
    IsCertified c := sorry

/-- A global Cech comparison packages refinement-natural stage maps together with the
elementwise filtered-colimit criterion.  Invertibility is derived from these stage conditions. -/
@[stacks 09UZ "certified open-cover Cech comparison datum"]
structure Comparison (p : ℕ) where
  /-- The coefficient-natural comparison at every open-cover refinement stage. -/
  map : RefinementComparison.{w, v, u} X p
  /-- The stage maps represent every target class and eventually kill every kernel class. -/
  isColimitIso : map.IsColimitIso

namespace Comparison

/-- Assemble a global Cech comparison from its refinement-natural map and colimit criterion. -/
def ofMap {p : ℕ} (map : RefinementComparison.{w, v, u} X p)
    (isColimitIso : map.IsColimitIso) : Comparison.{w, v, u} (X := X) p :=
  { map, isColimitIso }

/-- The concrete global morphism underlying a certified open-cover comparison. -/
abbrev hom {p : ℕ} (c : Comparison.{w, v, u} (X := X) p) :
    cohomologyFunctor.{w, v, u} X p ⟶
      liftedTargetCohomology.{w, v, u} X p :=
  comparison c.map

/-- The global comparison attached to stagewise colimit data is an isomorphism. -/
@[stacks 09UZ "open-cover Cech comparison isomorphism"]
theorem isIso {p : ℕ} (c : Comparison.{w, v, u} (X := X) p) :
    IsIso c.hom := c.isColimitIso.isCertified

/-- The global comparison isomorphism supplied by a certified comparison datum. -/
noncomputable def iso {p : ℕ} (c : Comparison.{w, v, u} (X := X) p) :
    cohomologyFunctor.{w, v, u} X p ≅
      liftedTargetCohomology.{w, v, u} X p :=
  @asIso _ _ _ _ c.hom (isIso c)

end Comparison

/-- The colimit comparison restricts at every refinement class to the supplied coverwise
comparison. -/
@[reassoc, stacks 09UZ "global Cech comparison on refinement stages"]
theorem ι_comp_comparison {p : ℕ}
    (c : RefinementComparison.{w, v, u} X p)
    (K : OpenCover.RefinementCategory.{v} X) :
    colimit.ι (liftedDiagram.{w, v, u} X p) K ≫ comparison c =
      (coefficientLift.{w, v, u} X).map (c.app K) := sorry

/-- At a fixed coefficient sheaf, the global comparison restricts to the supplied comparison at
the stage represented by an indexed open cover. -/
@[reassoc, stacks 09UZ "global Cech comparison on fixed-sheaf refinement stages"]
theorem stageMap_comp_comparison_app {p : ℕ}
    (c : RefinementComparison.{w, v, u} X p) (U : OpenCover.{v} X)
    (F : X.Sheaf AddCommGrpCat.{max u v w}) :
    stageMap.{w, v, u} U F p ≫ (comparison c).app F =
      TopCat.Presheaf.Cech.Colimit.universeLift.{max u v w}.map
        ((c.app U.refinementObject).app F) := sorry

/-- A certified comparison has the same stage restriction formula as its underlying natural
comparison datum. -/
@[reassoc, stacks 09UZ "certified Cech comparison on a refinement stage"]
theorem Comparison.stageMap_comp_hom {p : ℕ}
    (c : Comparison.{w, v, u} (X := X) p) (U : OpenCover.{v} X)
    (F : X.Sheaf AddCommGrpCat.{max u v w}) :
    stageMap.{w, v, u} U F p ≫ (c.hom).app F =
      TopCat.Presheaf.Cech.Colimit.universeLift.{max u v w}.map
        ((c.map.app U.refinementObject).app F) := sorry

end Comparison

end TopCat.Sheaf.Cohomology.Cech

