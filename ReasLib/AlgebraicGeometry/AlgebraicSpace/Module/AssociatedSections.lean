/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.FpqcPrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison

/-!
# Associated module sections on `(Spaces/X)_étale`

The abelian-group rule `F^a` sends `f : Y ⟶ X` to
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

/-- Pullback of sections along the identity in the slice is the identity. -/
theorem associatedPresheaf_map_id {X : AlgebraicSpace S} (F : X.Modules)
    (U : (Over X)ᵒᵖ) :
    (Modules.globalSectionsPullbackComp (𝟙 U).unop.left U.unop.hom F ≫
      eqToHom (congrArg (fun h ↦ Modules.globalSections ((Modules.pullback h).obj F))
        (Over.w (𝟙 U).unop))) =
      𝟙 (Modules.globalSections ((Modules.pullback U.unop.hom).obj F)) :=
  sorry

/-- Pullback of sections respects composition in the opposite slice. -/
theorem associatedPresheaf_map_comp {X : AlgebraicSpace S} (F : X.Modules)
    {U V W : (Over X)ᵒᵖ} (g : U ⟶ V) (h : V ⟶ W) :
    (Modules.globalSectionsPullbackComp (g ≫ h).unop.left U.unop.hom F ≫
      eqToHom (congrArg (fun h ↦ Modules.globalSections ((Modules.pullback h).obj F))
        (Over.w (g ≫ h).unop))) =
      (Modules.globalSectionsPullbackComp (g).unop.left U.unop.hom F ≫
      eqToHom (congrArg (fun h ↦ Modules.globalSections ((Modules.pullback h).obj F))
        (Over.w (g).unop))) ≫
      (Modules.globalSectionsPullbackComp (h).unop.left V.unop.hom F ≫
      eqToHom (congrArg (fun h ↦ Modules.globalSections ((Modules.pullback h).obj F))
        (Over.w (h).unop))) :=
  sorry

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
  map_id := associatedPresheaf_map_id F
  map_comp := associatedPresheaf_map_comp F

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
