/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.TwoCell
public import stacks_project.Chap96.Lemma_96_14_4_Restriction

/-!
# Atlas comparison squares for modules on a quotient stack

The atlas square of `[U / R]` supplies a 2-cell `x ∘ s ⟶ x ∘ t`. Together with
the comparison morphisms of 96.10.3.3, this is the diagram of modules on
`R_étale` that characterises the image of atlas restriction of Homs.
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
def atlasSource : G.R.left.toGroupoids ⟶ G.quotientStack :=
  AlgebraicSpace.toGroupoids.map G.s.left ≫ G.atlas

/-- `atlasSource` is `toGroupoids.map G.s.left` followed by the atlas. -/
theorem atlasSource_eq :
    atlasSource G = AlgebraicSpace.toGroupoids.map G.s.left ≫ G.atlas :=
  rfl

/-- The composite `x ∘ t : 𝒮_R ⟶ [U / R]`. -/
def atlasTarget : G.R.left.toGroupoids ⟶ G.quotientStack :=
  AlgebraicSpace.toGroupoids.map G.t.left ≫ G.atlas

/-- `atlasTarget` is `toGroupoids.map G.t.left` followed by the atlas. -/
theorem atlasTarget_eq :
    atlasTarget G = AlgebraicSpace.toGroupoids.map G.t.left ≫ G.atlas :=
  rfl

/-- The object inclusion of `𝒮_R` into `[U /ₚ R]` along `s`. -/
def atlasSourcePre : G.R.left.toGroupoids ⟶ G.preQuotient :=
  AlgebraicSpace.toGroupoids.map G.s.left ≫ G.atlasToPreQuotient

/-- `atlasSourcePre` is `toGroupoids.map G.s.left` followed by the object inclusion. -/
theorem atlasSourcePre_eq :
    atlasSourcePre G = AlgebraicSpace.toGroupoids.map G.s.left ≫ G.atlasToPreQuotient :=
  rfl

/-- The object inclusion of `𝒮_R` into `[U /ₚ R]` along `t`. -/
def atlasTargetPre : G.R.left.toGroupoids ⟶ G.preQuotient :=
  AlgebraicSpace.toGroupoids.map G.t.left ≫ G.atlasToPreQuotient

/-- `atlasTargetPre` is `toGroupoids.map G.t.left` followed by the object inclusion. -/
theorem atlasTargetPre_eq :
    atlasTargetPre G = AlgebraicSpace.toGroupoids.map G.t.left ≫ G.atlasToPreQuotient :=
  rfl

/-- The `R`-valued functor-of-points arrow carried by an object of `𝒮_R`. -/
def arrowPoint (x : G.R.left.toGroupoids.total) :
    G.R.left.functorOfPoints.obj x.unop.fst :=
  x.unop.snd

/-- `arrowPoint` is the fibre of the object of `𝒮_R`. -/
theorem arrowPoint_eq (x : G.R.left.toGroupoids.total) :
    arrowPoint G x = x.unop.snd :=
  rfl

/-- The source endpoint of `arrowPoint x` is the `U`-point of `x ∘ s`. -/
theorem arrowPoint_source (x : G.R.left.toGroupoids.total) :
    G.s.left.app x.unop.fst (arrowPoint G x) =
      ((toFunctor (atlasSourcePre G)).obj x).fiber :=
  sorry

/-- The target endpoint of `arrowPoint x` is the `U`-point of `x ∘ t`. -/
theorem arrowPoint_target (x : G.R.left.toGroupoids.total) :
    G.t.left.app x.unop.fst (arrowPoint G x) =
      ((toFunctor (atlasTargetPre G)).obj x).fiber :=
  sorry

/-- Inverse arrow of `arrowPoint x` along the groupoid inverse of `G`. -/
def arrowPointInv (x : G.R.left.toGroupoids.total) :
    G.R.left.functorOfPoints.obj x.unop.fst :=
  G.i.left.app x.unop.fst (arrowPoint G x)

/-- The source endpoint of the inverse arrow is the `U`-point of `x ∘ t`. -/
theorem arrowPointInv_source (x : G.R.left.toGroupoids.total) :
    G.s.left.app x.unop.fst (arrowPointInv G x) =
      ((toFunctor (atlasTargetPre G)).obj x).fiber :=
  sorry

/-- The target endpoint of the inverse arrow is the `U`-point of `x ∘ s`. -/
theorem arrowPointInv_target (x : G.R.left.toGroupoids.total) :
    G.t.left.app x.unop.fst (arrowPointInv G x) =
      ((toFunctor (atlasSourcePre G)).obj x).fiber :=
  sorry

/-- The morphism of `[U /ₚ R]` over `id_T` whose fibre is the `R`-arrow of `x`. -/
def sourceTargetPreApp (x : G.R.left.toGroupoids.total) :
    (toFunctor (atlasSourcePre G)).obj x ⟶ (toFunctor (atlasTargetPre G)).obj x where
  base := 𝟙 _
  fiber := FunctorPointHom.ofArrow (arrowPoint G x) sorry sorry

/-- The inverse morphism of `[U /ₚ R]` over `id_T` whose fibre is the inverse `R`-arrow. -/
def sourceTargetPreInvApp (x : G.R.left.toGroupoids.total) :
    (toFunctor (atlasTargetPre G)).obj x ⟶ (toFunctor (atlasSourcePre G)).obj x where
  base := 𝟙 _
  fiber := FunctorPointHom.ofArrow (arrowPointInv G x) sorry sorry

/-- The canonical 2-cell `π_p ∘ s ⟶ π_p ∘ t` of the atlas square, before stackification. -/
def sourceTargetPre : atlasSourcePre G ⟶ atlasTargetPre G :=
  ofBasedNatTrans
    { toNatTrans :=
        { app := fun x ↦ sourceTargetPreApp G x
          naturality := sorry }
      isHomLift' := sorry }

/-- The inverse 2-cell `π_p ∘ t ⟶ π_p ∘ s` of the atlas square, before stackification. -/
def sourceTargetPreInv : atlasTargetPre G ⟶ atlasSourcePre G :=
  ofBasedNatTrans
    { toNatTrans :=
        { app := fun x ↦ sourceTargetPreInvApp G x
          naturality := sorry }
      isHomLift' := sorry }

/-- Associator identifying `(s ≫ π_p) ≫ π` with `s ≫ (π_p ≫ π)`. -/
def atlasSourceIso : atlasSourcePre G ≫ G.stackificationHom ≅ atlasSource G :=
  α_ (AlgebraicSpace.toGroupoids.map G.s.left) G.atlasToPreQuotient G.stackificationHom

/-- Associator identifying `(t ≫ π_p) ≫ π` with `t ≫ (π_p ≫ π)`. -/
def atlasTargetIso : atlasTargetPre G ≫ G.stackificationHom ≅ atlasTarget G :=
  α_ (AlgebraicSpace.toGroupoids.map G.t.left) G.atlasToPreQuotient G.stackificationHom

/-- The canonical 2-cell `x ∘ s ⟶ x ∘ t` of the atlas square. -/
def sourceTarget : atlasSource G ⟶ atlasTarget G :=
  (atlasSourceIso G).inv ≫ (sourceTargetPre G ▷ G.stackificationHom) ≫ (atlasTargetIso G).hom

/-- The inverse 2-cell `x ∘ t ⟶ x ∘ s` of the atlas square. -/
def sourceTargetInv : atlasTarget G ⟶ atlasSource G :=
  (atlasTargetIso G).inv ≫ (sourceTargetPreInv G ▷ G.stackificationHom) ≫ (atlasSourceIso G).hom

/-- The invertible atlas 2-cell `x ∘ s ≅ x ∘ t`. -/
def sourceTargetIso : atlasSource G ≅ atlasTarget G where
  hom := sourceTarget G
  inv := sourceTargetInv G
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `sourceTargetIso` has underlying forward 2-cell `sourceTarget`. -/
theorem sourceTargetIso_hom : (sourceTargetIso G).hom = sourceTarget G :=
  rfl

/-- Algebraic-space morphism recovered from `toGroupoids.map G.s.left` along identity
presentations. -/
def sourceRecovered : G.R.left ⟶ G.U.left :=
  moduleComparisonSpaceMorphism (AlgebraicSpace.toGroupoids.map G.s.left)
    (idSpace G.R.left) (idSpace G.U.left)

/-- Recovering `toGroupoids.map G.s.left` along identity presentations returns `G.s.left`. -/
theorem sourceRecovered_eq : sourceRecovered G = G.s.left :=
  sorry

/-- Algebraic-space morphism recovered from `toGroupoids.map G.t.left` along identity
presentations. -/
def targetRecovered : G.R.left ⟶ G.U.left :=
  moduleComparisonSpaceMorphism (AlgebraicSpace.toGroupoids.map G.t.left)
    (idSpace G.R.left) (idSpace G.U.left)

/-- Recovering `toGroupoids.map G.t.left` along identity presentations returns `G.t.left`. -/
theorem targetRecovered_eq : targetRecovered G = G.t.left :=
  sorry

variable (M : RingedSite.ModuleCat.{u} (fppfRingedSite G.quotientStack))

/-- Restriction of `(x ∘ s)^* M` to the small étale site of `R`. -/
def atlasSourceModules : SheafOfModules.{u} (AlgebraicSpace.structureSheaf G.R.left) :=
  (restrictModules (idSpace G.R.left)).obj
    ((etaleModuleInverseImage (atlasSource G)).obj
      ((toEtaleRingedModules G.quotientStack).obj M))

/-- `atlasSourceModules` is restriction of the étale inverse image along `atlasSource`. -/
theorem atlasSourceModules_eq :
    atlasSourceModules G M =
      (restrictModules (idSpace G.R.left)).obj
        ((etaleModuleInverseImage (atlasSource G)).obj
          ((toEtaleRingedModules G.quotientStack).obj M)) :=
  rfl

/-- Restriction of `(x ∘ t)^* M` to the small étale site of `R`. -/
def atlasTargetModules : SheafOfModules.{u} (AlgebraicSpace.structureSheaf G.R.left) :=
  (restrictModules (idSpace G.R.left)).obj
    ((etaleModuleInverseImage (atlasTarget G)).obj
      ((toEtaleRingedModules G.quotientStack).obj M))

/-- `atlasTargetModules` is restriction of the étale inverse image along `atlasTarget`. -/
theorem atlasTargetModules_eq :
    atlasTargetModules G M =
      (restrictModules (idSpace G.R.left)).obj
        ((etaleModuleInverseImage (atlasTarget G)).obj
          ((toEtaleRingedModules G.quotientStack).obj M)) :=
  rfl

/-- The 96.10.3.3 comparison
`s_small^*(x^* M |_{U_étale}) ⟶ (x ∘ s)^* M |_{R_étale}`. -/
def sourceComparison :
    (AlgebraicSpace.Modules.pullback (sourceRecovered G)).obj (atlasRestrictModules G M) ⟶
      atlasSourceModules G M :=
  moduleComparisonSpace (AlgebraicSpace.toGroupoids.map G.s.left) (atlasSource G) G.atlas
    (eqToIso (atlasSource_eq G).symm) (idSpace G.R.left) (idSpace G.U.left)
    ((toEtaleRingedModules G.quotientStack).obj M)

/-- `sourceComparison` is `moduleComparisonSpace` for `s` and the atlas. -/
theorem sourceComparison_eq :
    sourceComparison G M =
      moduleComparisonSpace (AlgebraicSpace.toGroupoids.map G.s.left) (atlasSource G) G.atlas
        (eqToIso (atlasSource_eq G).symm) (idSpace G.R.left) (idSpace G.U.left)
        ((toEtaleRingedModules G.quotientStack).obj M) :=
  rfl

/-- The 96.10.3.3 comparison
`t_small^*(x^* M |_{U_étale}) ⟶ (x ∘ t)^* M |_{R_étale}`. -/
def targetComparison :
    (AlgebraicSpace.Modules.pullback (targetRecovered G)).obj (atlasRestrictModules G M) ⟶
      atlasTargetModules G M :=
  moduleComparisonSpace (AlgebraicSpace.toGroupoids.map G.t.left) (atlasTarget G) G.atlas
    (eqToIso (atlasTarget_eq G).symm) (idSpace G.R.left) (idSpace G.U.left)
    ((toEtaleRingedModules G.quotientStack).obj M)

/-- `targetComparison` is `moduleComparisonSpace` for `t` and the atlas. -/
theorem targetComparison_eq :
    targetComparison G M =
      moduleComparisonSpace (AlgebraicSpace.toGroupoids.map G.t.left) (atlasTarget G) G.atlas
        (eqToIso (atlasTarget_eq G).symm) (idSpace G.R.left) (idSpace G.U.left)
        ((toEtaleRingedModules G.quotientStack).obj M) :=
  rfl

/-- The atlas 2-cell as a map of modules on `R_étale`,
`(x ∘ t)^* M |_{R_étale} ⟶ (x ∘ s)^* M |_{R_étale}`. -/
def atlasAction : atlasTargetModules G M ⟶ atlasSourceModules G M :=
  (restrictModules (idSpace G.R.left)).map
    ((etaleModuleInverseImage_iso (sourceTargetIso G)).inv.app
      ((toEtaleRingedModules G.quotientStack).obj M))

/-- `atlasAction` is restriction of the inverse image of `sourceTargetIso`. -/
theorem atlasAction_eq :
    atlasAction G M =
      (restrictModules (idSpace G.R.left)).map
        ((etaleModuleInverseImage_iso (sourceTargetIso G)).inv.app
          ((toEtaleRingedModules G.quotientStack).obj M)) :=
  rfl

variable (F : QCoh G.quotientStack)
variable (H : RingedSite.ModuleCat.{u} (fppfRingedSite G.quotientStack))

/-- A map of restricted atlas pullbacks respects the 96.10.3.3 comparison diagram
on `R_étale` when both comparison squares commute and the middle maps agree under
the atlas 2-cell `(x ∘ s)^* ≅ (x ∘ t)^*`. -/
structure RespectsComparisons
    (φ : atlasRestrictModules G F.obj ⟶ atlasRestrictModules G H) : Prop where
  /-- The source comparison square commutes for some map of `(x ∘ s)^*` modules. -/
  source :
    ∃ ψs : atlasSourceModules G F.obj ⟶ atlasSourceModules G H,
      sourceComparison G F.obj ≫ ψs =
        (AlgebraicSpace.Modules.pullback (sourceRecovered G)).map φ ≫ sourceComparison G H
  /-- The target comparison square commutes for some map of `(x ∘ t)^*` modules. -/
  target :
    ∃ ψt : atlasTargetModules G F.obj ⟶ atlasTargetModules G H,
      targetComparison G F.obj ≫ ψt =
        (AlgebraicSpace.Modules.pullback (targetRecovered G)).map φ ≫ targetComparison G H
  /-- The two middle maps agree after identifying `(x ∘ s)^*` with `(x ∘ t)^*` via
  `sourceTarget`. -/
  compatible :
    ∃ (ψs : atlasSourceModules G F.obj ⟶ atlasSourceModules G H)
      (ψt : atlasTargetModules G F.obj ⟶ atlasTargetModules G H),
      sourceComparison G F.obj ≫ ψs =
          (AlgebraicSpace.Modules.pullback (sourceRecovered G)).map φ ≫
            sourceComparison G H ∧
        targetComparison G F.obj ≫ ψt =
          (AlgebraicSpace.Modules.pullback (targetRecovered G)).map φ ≫
            targetComparison G H ∧
        ψt ≫ atlasAction G H = atlasAction G F.obj ≫ ψs

namespace RespectsComparisons

/-- Construct `RespectsComparisons` from middle maps making both 96.10.3.3 squares
commute and agreeing under `atlasAction`. -/
def of {φ : atlasRestrictModules G F.obj ⟶ atlasRestrictModules G H}
    (ψs : atlasSourceModules G F.obj ⟶ atlasSourceModules G H)
    (ψt : atlasTargetModules G F.obj ⟶ atlasTargetModules G H)
    (h_source : sourceComparison G F.obj ≫ ψs =
      (AlgebraicSpace.Modules.pullback (sourceRecovered G)).map φ ≫ sourceComparison G H)
    (h_target : targetComparison G F.obj ≫ ψt =
      (AlgebraicSpace.Modules.pullback (targetRecovered G)).map φ ≫ targetComparison G H)
    (h_compat : ψt ≫ atlasAction G H = atlasAction G F.obj ≫ ψs) :
    RespectsComparisons G F H φ :=
  ⟨⟨ψs, h_source⟩, ⟨ψt, h_target⟩, ⟨ψs, ψt, h_source, h_target, h_compat⟩⟩

/-- `RespectsComparisons` is equivalent to the existence of middle maps making both
96.10.3.3 comparison squares commute and agreeing under the atlas 2-cell. -/
theorem iff {φ : atlasRestrictModules G F.obj ⟶ atlasRestrictModules G H} :
    RespectsComparisons G F H φ ↔
      ∃ (ψs : atlasSourceModules G F.obj ⟶ atlasSourceModules G H)
        (ψt : atlasTargetModules G F.obj ⟶ atlasTargetModules G H),
        sourceComparison G F.obj ≫ ψs =
            (AlgebraicSpace.Modules.pullback (sourceRecovered G)).map φ ≫
              sourceComparison G H ∧
          targetComparison G F.obj ≫ ψt =
            (AlgebraicSpace.Modules.pullback (targetRecovered G)).map φ ≫
              targetComparison G H ∧
          ψt ≫ atlasAction G H = atlasAction G F.obj ≫ ψs :=
  sorry

end RespectsComparisons

end AlgebraicGeometry.GroupoidsOver
