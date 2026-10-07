module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap74.Lemma_74_11_6_Precoverage
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization
public import stacks_project.Chap84.Lemma_84_6_4_Comparison

/-!
# Associated module sections on `(Spaces/X)_étale`

The source-facing abelian-group rule `F^a` sends `f : Y ⟶ X` to
`Γ(Y, f^* F)`. Quasi-coherence of `F` implies the sheaf condition for the
fpqc topology on `Over X`, and therefore also for fppf and étale.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The localized big fpqc topology on `Over X`, i.e. `(Spaces/X)_fpqc`. -/
abbrev overFpqcTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    GrothendieckTopology (Over X) :=
  (fpqcPrecoverage S).toGrothendieck.over X

/-- `overFpqcTopology X` is the localization of the fpqc Grothendieck topology
of algebraic spaces over `S` at `X`. -/
theorem overFpqcTopology_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    overFpqcTopology X = (fpqcPrecoverage S).toGrothendieck.over X :=
  rfl

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

variable {S : Scheme.{u}}

/-- The abelian-group rule `F^a` on `(Spaces/X)_étale`, sending
`(f : Y ⟶ X)` to `Γ(Y, f^* F)`. -/
def associatedPresheaf {X : AlgebraicSpace S} (F : X.Modules) :
    (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := Modules.globalSections ((Modules.pullback U.unop.hom).obj F)
  map {U V} g :=
    Modules.globalSectionsPullbackComp g.unop.left U.unop.hom F ≫
      eqToHom
        (congrArg (fun h ↦ Modules.globalSections ((Modules.pullback h).obj F))
          (Over.w g.unop))
  map_id := sorry
  map_comp := sorry

/-- The value of `associatedPresheaf F` at `U` is `Γ(U.left, U.hom^* F)`. -/
theorem associatedPresheaf_obj {X : AlgebraicSpace S} (F : X.Modules) (U : Over X) :
    (associatedPresheaf F).obj (op U) =
      Modules.globalSections ((Modules.pullback U.hom).obj F) :=
  rfl

/-- Restriction in `associatedPresheaf F` along `g : V ⟶ U` over `X` is
global-sections pullback along `g.left`, compared along the Over triangle. -/
theorem associatedPresheaf_map {X : AlgebraicSpace S} (F : X.Modules)
    {U V : Over X} (g : V ⟶ U) :
    (associatedPresheaf F).map g.op =
      Modules.globalSectionsPullbackComp g.left U.hom F ≫
        eqToHom
          (congrArg (fun h ↦ Modules.globalSections ((Modules.pullback h).obj F))
            (Over.w g)) :=
  rfl

/-- The associated abelian-group rule is a sheaf for the fpqc topology on
`(Spaces/X)`. -/
theorem associatedPresheaf_isSheaf_fpqc {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf (overFpqcTopology X) (associatedPresheaf F) :=
  sorry

/-- The associated abelian-group rule is a sheaf for the fppf topology on
`(Spaces/X)`. -/
theorem associatedPresheaf_isSheaf_fppf {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf (overFppfTopology X) (associatedPresheaf F) :=
  sorry

/-- The associated abelian-group rule is a sheaf for the étale topology on
`(Spaces/X)`. -/
theorem associatedPresheaf_isSheaf_etale {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf (overEtaleTopology X) (associatedPresheaf F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
