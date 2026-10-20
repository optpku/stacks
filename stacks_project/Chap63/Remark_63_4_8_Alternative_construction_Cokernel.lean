/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap63.Lemma_63_3_17
public import stacks_project.Chap63.Lemma_63_4_1
public import stacks_project.Chap63.Remark_63_4_8_Alternative_construction_Cech

/-!
# Alternative cokernel construction of locally quasi-finite lower shriek

For an open family with separated restrictions, `f_! F` is realized as the
cokernel of the separated Čech penultimate map, functorially in `F`.
-/

@[expose] public section

open CategoryTheory hiding Over
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable {ι : Type u} (𝒰 : ι → X.Opens)
variable [∀ i, IsSeparated ((𝒰 i).ι ≫ f)]

/-- Sheafification of Lemma 63.4.1 identifies a separated Čech summand with the
corresponding locally quasi-finite lower-shriek summand. -/
def etaleLowerShriekCechSummandIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (σ : Fin (n + 1) → ι) :
    etaleLowerShriekCechSummand f 𝒰 F n σ ≅
      lowerShriekCechSummand f 𝒰 F n σ :=
  (asIso
      ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).counit.app
        (etaleLowerShriekCechSummand f 𝒰 F n σ))).symm ≪≫
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).mapIso
      ((lowerShriekPresheafIso
          ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f)).app
        ((etaleRestrictionSheaf (lowerShriekCechIntersection 𝒰 σ).ι
            AddCommGrpCat.{u}).obj F)).symm

/-- Coproduct of the summand identifications of Lemma 63.4.1. -/
def etaleLowerShriekCechTermIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    etaleLowerShriekCechTerm f 𝒰 F n ≅ lowerShriekCechTerm f 𝒰 F n :=
  Sigma.mapIso (etaleLowerShriekCechSummandIso f 𝒰 F n)

/-- The alternative compact-support direct image, as the cokernel of the
separated Čech penultimate map. -/
def lowerShriekCechCokernel
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  cokernel (etaleLowerShriekCechPenultimate f 𝒰 F)

/-- The cokernel projection from the degree-zero separated Čech term. -/
abbrev lowerShriekCechCokernel_π
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekCechTerm f 𝒰 F 0 ⟶ lowerShriekCechCokernel f 𝒰 F :=
  cokernel.π (etaleLowerShriekCechPenultimate f 𝒰 F)

/-- The cokernel universal property of the alternative construction. -/
abbrev lowerShriekCechCokernel_desc
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
    (k : etaleLowerShriekCechTerm f 𝒰 F 0 ⟶ G)
    (h : etaleLowerShriekCechPenultimate f 𝒰 F ≫ k = 0) :
    lowerShriekCechCokernel f 𝒰 F ⟶ G :=
  cokernel.desc (etaleLowerShriekCechPenultimate f 𝒰 F) k h

/-- The cokernel projection is the canonical map out of the degree-zero term. -/
theorem lowerShriekCechCokernel_π_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekCechCokernel_π f 𝒰 F =
      cokernel.π (etaleLowerShriekCechPenultimate f 𝒰 F) :=
  sorry

/-- A morphism of abelian étale sheaves acts on the alternative cokernel by
`cokernel.map`. -/
def lowerShriekCechCokernelMap
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    lowerShriekCechCokernel f 𝒰 F ⟶ lowerShriekCechCokernel f 𝒰 G :=
  cokernel.map (etaleLowerShriekCechPenultimate f 𝒰 F)
    (etaleLowerShriekCechPenultimate f 𝒰 G)
    (etaleLowerShriekCechTermMap f 𝒰 φ 1) (etaleLowerShriekCechTermMap f 𝒰 φ 0)
    (etaleLowerShriekCechPenultimate_naturality f 𝒰 φ)

/-- The functor sending an abelian étale sheaf to the cokernel of the separated
Čech penultimate map. -/
def lowerShriekCechCokernelFunctor :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  obj := lowerShriekCechCokernel f 𝒰
  map := lowerShriekCechCokernelMap f 𝒰
  map_id := sorry
  map_comp := sorry

/-- Evaluating the alternative functor recovers the objectwise cokernel. -/
theorem lowerShriekCechCokernelFunctor_obj
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekCechCokernelFunctor f 𝒰).obj F =
      lowerShriekCechCokernel f 𝒰 F :=
  sorry

/-- The alternative functor acts on morphisms by `lowerShriekCechCokernelMap`. -/
theorem lowerShriekCechCokernelFunctor_map
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (lowerShriekCechCokernelFunctor f 𝒰).map φ =
      lowerShriekCechCokernelMap f 𝒰 φ :=
  sorry

/-- The transported augmentation annihilates the separated penultimate map. -/
theorem etaleLowerShriekCechPenultimate_comp_augmentation
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekCechPenultimate f 𝒰 F ≫
        (etaleLowerShriekCechTermIso f 𝒰 F 0).hom ≫
          lowerShriekCechAugmentation f 𝒰 F = 0 :=
  sorry

/-- Comparison from the alternative cokernel to the canonical `f_! F`, induced
by the Čech augmentation of Lemma 63.4.7 after the identifications of
Lemma 63.4.1. -/
def lowerShriekCechCokernelComparison
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekCechCokernel f 𝒰 F ⟶ (lowerShriek f).obj F :=
  cokernel.desc (etaleLowerShriekCechPenultimate f 𝒰 F)
    ((etaleLowerShriekCechTermIso f 𝒰 F 0).hom ≫
      lowerShriekCechAugmentation f 𝒰 F)
    (etaleLowerShriekCechPenultimate_comp_augmentation f 𝒰 F)

/-- On an open covering, the comparison morphism is an isomorphism. -/
theorem lowerShriekCechCokernelComparison_isIso (h𝒰 : IsOpenCover 𝒰)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (lowerShriekCechCokernelComparison f 𝒰 F) :=
  sorry

/-- The inverse comparison, obtained from
`lowerShriekCechCokernelComparison_isIso`. -/
def lowerShriekCechCokernelComparisonInv (h𝒰 : IsOpenCover 𝒰)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek f).obj F ⟶ lowerShriekCechCokernel f 𝒰 F :=
  @inv _ _ _ _ (lowerShriekCechCokernelComparison f 𝒰 F)
    (lowerShriekCechCokernelComparison_isIso f 𝒰 h𝒰 F)

/-- On an open covering, the alternative cokernel functor is canonically
isomorphic to `lowerShriek`. -/
def lowerShriekCechCokernelIso (h𝒰 : IsOpenCover 𝒰) :
    lowerShriekCechCokernelFunctor f 𝒰 ≅ lowerShriek f :=
  NatIso.ofComponents
    (fun F ↦
      { hom := lowerShriekCechCokernelComparison f 𝒰 F
        inv := lowerShriekCechCokernelComparisonInv f 𝒰 h𝒰 F
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- A geometric point of an open `U ⊆ X` over `ȳ` yields a geometric point of
`X` over `ȳ` by composing with `U.ι`. -/
def restrictOpensOver {U : X.Opens} (ybar : GeometricPoint Y)
    (x : Over (U.ι ≫ f) ybar) : Over f ybar where
  toScheme := x.toScheme ≫ U.ι
  fac := (Category.assoc x.toScheme U.ι f).trans x.fac

/-- Sections of `F|_U` on an étale `U`-scheme agree with sections of `F` on the
same scheme viewed over `X`. -/
def etaleRestrictionOpensSectionsIso {U : X.Opens}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : (U : Scheme.{u}).Etale) :
    ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F).obj.obj (op V) ≅
      F.obj.obj (op ((etaleRestriction U.ι).obj V)) :=
  (etaleRestriction U.ι).sheafPushforwardContinuousObjObjIso AddCommGrpCat.{u} F V

/-- A lift of a geometric point of `U` over `ȳ` to an étale `U`-scheme is the
same lift of the image point of `X`. -/
def restrictionOpensFiberElement {U : X.Opens} (ybar : GeometricPoint Y)
    (x : Over (U.ι ≫ f) ybar) (V : (U : Scheme.{u}).Etale)
    (φ : (toSmallEtalePoint x.toGeometricPoint).fiber.obj V) :
    (toSmallEtalePoint (restrictOpensOver f ybar x).toGeometricPoint).fiber.obj
      ((etaleRestriction U.ι).obj V) :=
  (CategoryTheory.Over.homMk φ.left sorry :
    (toSmallEtalePoint (restrictOpensOver f ybar x).toGeometricPoint).fiber.obj
      ((etaleRestriction U.ι).obj V))

/-- Identification of the stalk of `F|_U` at a geometric point of `U` over `ȳ`
with the stalk of `F` at the image geometric point of `X`. -/
def restrictionOpensSheafFiber {U : X.Opens} (ybar : GeometricPoint Y)
    (x : Over (U.ι ≫ f) ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F) ⟶
      (toSmallEtalePoint
          (restrictOpensOver f ybar x).toGeometricPoint).sheafFiber.obj F :=
  (toSmallEtalePoint x.toGeometricPoint).presheafFiberDesc
    (fun V φ ↦
      (etaleRestrictionOpensSectionsIso F V).hom ≫
        (toSmallEtalePoint
            (restrictOpensOver f ybar x).toGeometricPoint).toPresheafFiber
          ((etaleRestriction U.ι).obj V)
          (restrictionOpensFiberElement f ybar x V φ) F.1)
    sorry

/-- Inclusion of fibrewise stalk coproducts along a Zariski open of the source. -/
def abelianStalkCoproductOpens {U : X.Opens} (ybar : GeometricPoint Y) :
    etaleRestrictionSheaf U.ι AddCommGrpCat.{u} ⋙
        abelianStalkCoproduct (U.ι ≫ f) ybar ⟶
      abelianStalkCoproduct f ybar where
  app F :=
    Sigma.map' (restrictOpensOver f ybar) fun x ↦
      restrictionOpensSheafFiber f ybar x F
  naturality := sorry

/-- Stalks of a separated Čech summand compare with the fibrewise coproduct of
Lemma 63.3.17, then include into the fibrewise coproduct of `f`. -/
def etaleLowerShriekCechSummandStalkToCoproduct (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ)
    (σ : Fin (n + 1) → ι) :
    (toSmallEtalePoint ybar).sheafFiber.obj
        (etaleLowerShriekCechSummand f 𝒰 F n σ) ⟶
      (abelianStalkCoproduct f ybar).obj F :=
  (etaleLowerShriekStalkIso
        ((lowerShriekCechIntersection 𝒰 σ).ι ≫ f) ybar).hom.app
      ((etaleRestrictionSheaf (lowerShriekCechIntersection 𝒰 σ).ι
          AddCommGrpCat.{u}).obj F) ≫
    (abelianStalkCoproductOpens f ybar).app F

/-- The coproduct comparison of stalks of separated Čech summands is an
isomorphism. -/
theorem isIso_sigmaComparison_etaleLowerShriekCechSummand
    (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    IsIso
      (sigmaComparison (toSmallEtalePoint ybar).sheafFiber
        (etaleLowerShriekCechSummand f 𝒰 F n)) :=
  sorry

/-- The map from the stalk of the degree-zero separated Čech term to the
fibrewise coproduct of stalks of `F`. -/
def etaleLowerShriekCechTermStalkToCoproduct (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint ybar).sheafFiber.obj
        (etaleLowerShriekCechTerm f 𝒰 F 0) ⟶
      (abelianStalkCoproduct f ybar).obj F :=
  @inv _ _ _ _
      (sigmaComparison (toSmallEtalePoint ybar).sheafFiber
        (etaleLowerShriekCechSummand f 𝒰 F 0))
      (isIso_sigmaComparison_etaleLowerShriekCechSummand f 𝒰 ybar F 0) ≫
    Sigma.desc (etaleLowerShriekCechSummandStalkToCoproduct f 𝒰 ybar F 0)

/-- The stalk of the penultimate map annihilates under the fibrewise coproduct
comparison. -/
theorem etaleLowerShriekCechPenultimate_sheafFiber_comp
    (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint ybar).sheafFiber.map
          (etaleLowerShriekCechPenultimate f 𝒰 F) ≫
        etaleLowerShriekCechTermStalkToCoproduct f 𝒰 ybar F = 0 :=
  sorry

/-- Stalks preserve the cokernel of the separated Čech penultimate map. -/
theorem isIso_cokernelComparison_etaleLowerShriekCechPenultimate
    (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso
      (cokernelComparison (etaleLowerShriekCechPenultimate f 𝒰 F)
        (toSmallEtalePoint ybar).sheafFiber) :=
  sorry

/-- Comparison from the stalk of the alternative cokernel to the fibrewise
coproduct of Lemma 63.4.5, assembled from Lemma 63.3.17 on cover members. -/
def lowerShriekCechCokernelStalkComparison (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint ybar).sheafFiber.obj
        ((lowerShriekCechCokernelFunctor f 𝒰).obj F) ⟶
      (abelianStalkCoproduct f ybar).obj F :=
  @inv _ _ _ _
      (cokernelComparison (etaleLowerShriekCechPenultimate f 𝒰 F)
        (toSmallEtalePoint ybar).sheafFiber)
      (isIso_cokernelComparison_etaleLowerShriekCechPenultimate f 𝒰 ybar F) ≫
    cokernel.desc
      ((toSmallEtalePoint ybar).sheafFiber.map
        (etaleLowerShriekCechPenultimate f 𝒰 F))
      (etaleLowerShriekCechTermStalkToCoproduct f 𝒰 ybar F)
      (etaleLowerShriekCechPenultimate_sheafFiber_comp f 𝒰 ybar F)

/-- On an open covering, the stalk comparison is an isomorphism. -/
theorem lowerShriekCechCokernelStalkComparison_isIso (h𝒰 : IsOpenCover 𝒰)
    (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (lowerShriekCechCokernelStalkComparison f 𝒰 ybar F) :=
  sorry

/-- The inverse of the stalk comparison. -/
def lowerShriekCechCokernelStalkComparisonInv (h𝒰 : IsOpenCover 𝒰)
    (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianStalkCoproduct f ybar).obj F ⟶
      (toSmallEtalePoint ybar).sheafFiber.obj
        ((lowerShriekCechCokernelFunctor f 𝒰).obj F) :=
  @inv _ _ _ _ (lowerShriekCechCokernelStalkComparison f 𝒰 ybar F)
    (lowerShriekCechCokernelStalkComparison_isIso f 𝒰 h𝒰 ybar F)

/-- On an open covering, stalks of the alternative construction recover the
coproduct formula `(f_! F)_ȳ ≅ ⊕_{f(x̄)=ȳ} F_x̄`. -/
def lowerShriekCechCokernelStalkIso (h𝒰 : IsOpenCover 𝒰)
    (ybar : GeometricPoint Y) :
    lowerShriekCechCokernelFunctor f 𝒰 ⋙
        (toSmallEtalePoint ybar).sheafFiber ≅
      abelianStalkCoproduct f ybar :=
  NatIso.ofComponents
    (fun F ↦
      { hom := lowerShriekCechCokernelStalkComparison f 𝒰 ybar F
        inv := lowerShriekCechCokernelStalkComparisonInv f 𝒰 h𝒰 ybar F
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end AlgebraicGeometry.Scheme.Etale

end
