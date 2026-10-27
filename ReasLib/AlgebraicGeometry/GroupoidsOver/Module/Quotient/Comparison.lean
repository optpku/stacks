/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quotient.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small.Comparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.SpaceComparison

/-!
# Atlas comparison squares for modules on a quotient stack

The atlas square of `[U / R]` supplies a 2-cell `x ∘ s ⟶ x ∘ t`. Together with
the canonical small-étale comparison morphisms, this gives a diagram of modules
on `R_étale` and a compatibility predicate for maps of atlas restrictions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- The composite `x ∘ s : 𝒮_R ⟶ [U / R]`. -/
def atlasSource : G.R.left.toGroupoids ⟶ (SmallQuotient.quotientStack G) :=
  AlgebraicSpace.toGroupoids.map G.s.left ≫ (SmallQuotient.atlas G)

/-- `atlasSource` is `toGroupoids.map G.s.left` followed by the atlas. -/
theorem atlasSource_eq :
    atlasSource G = AlgebraicSpace.toGroupoids.map G.s.left ≫ (SmallQuotient.atlas G) :=
  rfl

/-- The composite `x ∘ t : 𝒮_R ⟶ [U / R]`. -/
def atlasTarget : G.R.left.toGroupoids ⟶ (SmallQuotient.quotientStack G) :=
  AlgebraicSpace.toGroupoids.map G.t.left ≫ (SmallQuotient.atlas G)

/-- `atlasTarget` is `toGroupoids.map G.t.left` followed by the atlas. -/
theorem atlasTarget_eq :
    atlasTarget G = AlgebraicSpace.toGroupoids.map G.t.left ≫ (SmallQuotient.atlas G) :=
  rfl

/-- Algebraic-space morphism recovered from `toGroupoids.map G.s.left` along identity
presentations. -/
def sourceRecovered : G.R.left ⟶ G.U.left :=
  moduleComparisonSpaceMorphism (AlgebraicSpace.toGroupoids.map G.s.left)
    (Bicategory.Equivalence.id G.R.left.toGroupoids) (Bicategory.Equivalence.id G.U.left.toGroupoids)

/-- Recovering `toGroupoids.map G.s.left` along identity presentations returns `G.s.left`. -/
theorem sourceRecovered_eq : sourceRecovered G = G.s.left :=
  sorry

/-- Algebraic-space morphism recovered from `toGroupoids.map G.t.left` along identity
presentations. -/
def targetRecovered : G.R.left ⟶ G.U.left :=
  moduleComparisonSpaceMorphism (AlgebraicSpace.toGroupoids.map G.t.left)
    (Bicategory.Equivalence.id G.R.left.toGroupoids) (Bicategory.Equivalence.id G.U.left.toGroupoids)

/-- Recovering `toGroupoids.map G.t.left` along identity presentations returns `G.t.left`. -/
theorem targetRecovered_eq : targetRecovered G = G.t.left :=
  sorry

variable (M : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G)))

/-- Restriction of `(x ∘ s)^* M` to the small étale site of `R`. -/
def atlasSourceModules : SheafOfModules.{u} (AlgebraicSpace.structureSheaf G.R.left) :=
  (restrictModules (Bicategory.Equivalence.id G.R.left.toGroupoids)).obj
    ((etaleModuleInverseImage (atlasSource G)).obj
      ((toEtaleModules (SmallQuotient.quotientStack G)).obj M))

/-- `atlasSourceModules` is restriction of the étale inverse image along `atlasSource`. -/
theorem atlasSourceModules_eq :
    atlasSourceModules G M =
      (restrictModules (Bicategory.Equivalence.id G.R.left.toGroupoids)).obj
        ((etaleModuleInverseImage (atlasSource G)).obj
          ((toEtaleModules (SmallQuotient.quotientStack G)).obj M)) :=
  rfl

/-- Restriction of `(x ∘ t)^* M` to the small étale site of `R`. -/
def atlasTargetModules : SheafOfModules.{u} (AlgebraicSpace.structureSheaf G.R.left) :=
  (restrictModules (Bicategory.Equivalence.id G.R.left.toGroupoids)).obj
    ((etaleModuleInverseImage (atlasTarget G)).obj
      ((toEtaleModules (SmallQuotient.quotientStack G)).obj M))

/-- `atlasTargetModules` is restriction of the étale inverse image along `atlasTarget`. -/
theorem atlasTargetModules_eq :
    atlasTargetModules G M =
      (restrictModules (Bicategory.Equivalence.id G.R.left.toGroupoids)).obj
        ((etaleModuleInverseImage (atlasTarget G)).obj
          ((toEtaleModules (SmallQuotient.quotientStack G)).obj M)) :=
  rfl

/-- The canonical comparison
`s_small^*(x^* M |_{U_étale}) ⟶ (x ∘ s)^* M |_{R_étale}`. -/
def sourceComparison :
    (AlgebraicSpace.Modules.pullback (sourceRecovered G)).obj (atlasRestrictModules G M) ⟶
      atlasSourceModules G M :=
  moduleComparisonSpace (AlgebraicSpace.toGroupoids.map G.s.left) (atlasSource G) (SmallQuotient.atlas G)
    (eqToIso (atlasSource_eq G).symm) (Bicategory.Equivalence.id G.R.left.toGroupoids) (Bicategory.Equivalence.id G.U.left.toGroupoids)
    ((toEtaleModules (SmallQuotient.quotientStack G)).obj M)

/-- `sourceComparison` is `moduleComparisonSpace` for `s` and the atlas. -/
theorem sourceComparison_eq :
    sourceComparison G M =
      moduleComparisonSpace (AlgebraicSpace.toGroupoids.map G.s.left) (atlasSource G) (SmallQuotient.atlas G)
        (eqToIso (atlasSource_eq G).symm) (Bicategory.Equivalence.id G.R.left.toGroupoids) (Bicategory.Equivalence.id G.U.left.toGroupoids)
        ((toEtaleModules (SmallQuotient.quotientStack G)).obj M) :=
  rfl

/-- The canonical comparison
`t_small^*(x^* M |_{U_étale}) ⟶ (x ∘ t)^* M |_{R_étale}`. -/
def targetComparison :
    (AlgebraicSpace.Modules.pullback (targetRecovered G)).obj (atlasRestrictModules G M) ⟶
      atlasTargetModules G M :=
  moduleComparisonSpace (AlgebraicSpace.toGroupoids.map G.t.left) (atlasTarget G) (SmallQuotient.atlas G)
    (eqToIso (atlasTarget_eq G).symm) (Bicategory.Equivalence.id G.R.left.toGroupoids) (Bicategory.Equivalence.id G.U.left.toGroupoids)
    ((toEtaleModules (SmallQuotient.quotientStack G)).obj M)

/-- `targetComparison` is `moduleComparisonSpace` for `t` and the atlas. -/
theorem targetComparison_eq :
    targetComparison G M =
      moduleComparisonSpace (AlgebraicSpace.toGroupoids.map G.t.left) (atlasTarget G) (SmallQuotient.atlas G)
        (eqToIso (atlasTarget_eq G).symm) (Bicategory.Equivalence.id G.R.left.toGroupoids) (Bicategory.Equivalence.id G.U.left.toGroupoids)
        ((toEtaleModules (SmallQuotient.quotientStack G)).obj M) :=
  rfl

/-- The atlas 2-cell as a map of modules on `R_étale`,
`(x ∘ t)^* M |_{R_étale} ⟶ (x ∘ s)^* M |_{R_étale}`. -/
def atlasAction : atlasTargetModules G M ⟶ atlasSourceModules G M :=
  (restrictModules (Bicategory.Equivalence.id G.R.left.toGroupoids)).map
    ((etaleModuleInverseImage_iso (SmallQuotient.sourceTargetIso G)).inv.app
      ((toEtaleModules (SmallQuotient.quotientStack G)).obj M))

/-- `atlasAction` is restriction of the inverse image of the canonical source–target isomorphism. -/
theorem atlasAction_eq :
    atlasAction G M =
      (restrictModules (Bicategory.Equivalence.id G.R.left.toGroupoids)).map
        ((etaleModuleInverseImage_iso (SmallQuotient.sourceTargetIso G)).inv.app
          ((toEtaleModules (SmallQuotient.quotientStack G)).obj M)) :=
  rfl

variable (F : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G)))
variable (H : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G)))

/-- A map of restricted atlas pullbacks respects the canonical comparison diagram
on `R_étale` when both comparison squares commute and the middle maps agree under
the atlas 2-cell `(x ∘ s)^* ≅ (x ∘ t)^*`. -/
structure RespectsComparisons
    (φ : atlasRestrictModules G F ⟶ atlasRestrictModules G H) : Prop where
  /-- The source comparison square commutes for some map of `(x ∘ s)^*` modules. -/
  source :
    ∃ ψs : atlasSourceModules G F ⟶ atlasSourceModules G H,
      sourceComparison G F ≫ ψs =
        (AlgebraicSpace.Modules.pullback (sourceRecovered G)).map φ ≫ sourceComparison G H
  /-- The target comparison square commutes for some map of `(x ∘ t)^*` modules. -/
  target :
    ∃ ψt : atlasTargetModules G F ⟶ atlasTargetModules G H,
      targetComparison G F ≫ ψt =
        (AlgebraicSpace.Modules.pullback (targetRecovered G)).map φ ≫ targetComparison G H
  /-- The two middle maps agree after identifying `(x ∘ s)^*` with `(x ∘ t)^*` via
  the canonical source–target isomorphism. -/
  compatible :
    ∃ (ψs : atlasSourceModules G F ⟶ atlasSourceModules G H)
      (ψt : atlasTargetModules G F ⟶ atlasTargetModules G H),
      sourceComparison G F ≫ ψs =
          (AlgebraicSpace.Modules.pullback (sourceRecovered G)).map φ ≫
            sourceComparison G H ∧
        targetComparison G F ≫ ψt =
          (AlgebraicSpace.Modules.pullback (targetRecovered G)).map φ ≫
            targetComparison G H ∧
        ψt ≫ atlasAction G H = atlasAction G F ≫ ψs

namespace RespectsComparisons

/-- Construct `RespectsComparisons` from middle maps making both comparison squares
commute and agreeing under `atlasAction`. -/
def of {φ : atlasRestrictModules G F ⟶ atlasRestrictModules G H}
    (ψs : atlasSourceModules G F ⟶ atlasSourceModules G H)
    (ψt : atlasTargetModules G F ⟶ atlasTargetModules G H)
    (h_source : sourceComparison G F ≫ ψs =
      (AlgebraicSpace.Modules.pullback (sourceRecovered G)).map φ ≫ sourceComparison G H)
    (h_target : targetComparison G F ≫ ψt =
      (AlgebraicSpace.Modules.pullback (targetRecovered G)).map φ ≫ targetComparison G H)
    (h_compat : ψt ≫ atlasAction G H = atlasAction G F ≫ ψs) :
    RespectsComparisons G F H φ :=
  ⟨⟨ψs, h_source⟩, ⟨ψt, h_target⟩, ⟨ψs, ψt, h_source, h_target, h_compat⟩⟩

/-- `RespectsComparisons` is equivalent to the existence of middle maps making both
canonical comparison squares commute and agreeing under the atlas 2-cell. -/
theorem iff {φ : atlasRestrictModules G F ⟶ atlasRestrictModules G H} :
    RespectsComparisons G F H φ ↔
      ∃ (ψs : atlasSourceModules G F ⟶ atlasSourceModules G H)
        (ψt : atlasTargetModules G F ⟶ atlasTargetModules G H),
        sourceComparison G F ≫ ψs =
            (AlgebraicSpace.Modules.pullback (sourceRecovered G)).map φ ≫
              sourceComparison G H ∧
          targetComparison G F ≫ ψt =
            (AlgebraicSpace.Modules.pullback (targetRecovered G)).map φ ≫
              targetComparison G H ∧
          ψt ≫ atlasAction G H = atlasAction G F ≫ ψs :=
  sorry

end RespectsComparisons

end AlgebraicGeometry.GroupoidsOver
