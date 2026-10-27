/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.SeparatedQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Cech.Cokernel

/-!
# Stalks of separated Čech cokernels

The separated stalk formula induces explicit coproduct and cokernel comparison
maps, identifying stalks of the Čech cokernel with same-field stalk coproducts.
-/

@[expose] public section

open CategoryTheory
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

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must retain this private restriction map in the public stalk composite.
set_option backward.privateInPublic true in
/-- A geometric point of an open `U ⊆ X` over `ȳ` yields a geometric point of
`X` over `ȳ` by composing with `U.ι`. -/
private def restrictOpensFiber {U : X.Opens} (ybar : GeometricPoint Y)
    (x : Fiber (U.ι ≫ f) ybar) : Fiber f ybar :=
  Fiber.of (x.lift ≫ U.ι) ((Category.assoc x.lift U.ι f).trans x.fac)

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must retain this private restriction map in the public stalk composite.
set_option backward.privateInPublic true in
/-- Sections of `F|_U` on an étale `U`-scheme agree with sections of `F` on the
same scheme viewed over `X`. -/
private def etaleRestrictionOpensSectionsIso {U : X.Opens}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : (U : Scheme.{u}).Etale) :
    ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F).obj.obj (op V) ≅
      F.obj.obj (op ((etaleRestriction U.ι).obj V)) :=
  (etaleRestriction U.ι).sheafPushforwardContinuousObjObjIso AddCommGrpCat.{u} F V

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must retain this private restriction map in the public stalk composite.
set_option backward.privateInPublic true in
/-- A lift of a geometric point of `U` over `ȳ` to an étale `U`-scheme is the
same lift of the image point of `X`. -/
private def restrictionOpensFiberElement {U : X.Opens} (ybar : GeometricPoint Y)
    (x : Fiber (U.ι ≫ f) ybar) (V : (U : Scheme.{u}).Etale)
    (φ : (toSmallEtalePoint x.point).fiber.obj V) :
    (toSmallEtalePoint (restrictOpensFiber f ybar x).point).fiber.obj
      ((etaleRestriction U.ι).obj V) :=
  (CategoryTheory.Over.homMk φ.left sorry :
    (toSmallEtalePoint (restrictOpensFiber f ybar x).point).fiber.obj
      ((etaleRestriction U.ι).obj V))

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must retain this private restriction map in the public stalk composite.
set_option backward.privateInPublic true in
/-- Identification of the stalk of `F|_U` at a geometric point of `U` over `ȳ`
with the stalk of `F` at the image geometric point of `X`. -/
private def restrictionOpensSheafFiber {U : X.Opens} (ybar : GeometricPoint Y)
    (x : Fiber (U.ι ≫ f) ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint x.point).sheafFiber.obj
        ((etaleRestrictionSheaf U.ι AddCommGrpCat.{u}).obj F) ⟶
      (toSmallEtalePoint
          (restrictOpensFiber f ybar x).point).sheafFiber.obj F :=
  (toSmallEtalePoint x.point).presheafFiberDesc
    (fun V φ ↦
      (etaleRestrictionOpensSectionsIso F V).hom ≫
        (toSmallEtalePoint
            (restrictOpensFiber f ybar x).point).toPresheafFiber
          ((etaleRestriction U.ι).obj V)
          (restrictionOpensFiberElement f ybar x V φ) F.1)
    sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator must retain this private restriction map in the public stalk composite.
set_option backward.privateInPublic true in
/-- Inclusion of fibrewise stalk coproducts along a Zariski open of the source. -/
private def abelianStalkCoproductOpens {U : X.Opens} (ybar : GeometricPoint Y) :
    etaleRestrictionSheaf U.ι AddCommGrpCat.{u} ⋙
        abelianStalkCoproduct (U.ι ≫ f) ybar ⟶
      abelianStalkCoproduct f ybar where
  app F :=
    Sigma.map' (restrictOpensFiber f ybar) fun x ↦
      restrictionOpensSheafFiber f ybar x F
  naturality := sorry

-- Local declaration justification (metaprogramming implementation): Lean's module
-- elaborator needs the five private restriction maps to expose this public composite.
set_option backward.privateInPublic true in
/-- Stalks of a separated Čech summand compare with the same-field fibrewise
coproduct, then include into the fibrewise coproduct of `f`. -/
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
instance isIso_sigmaComparison_etaleLowerShriekCechSummand
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
  @CategoryTheory.inv _ _ _ _
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
instance isIso_cokernelComparison_etaleLowerShriekCechPenultimate
    (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso
      (cokernelComparison (etaleLowerShriekCechPenultimate f 𝒰 F)
        (toSmallEtalePoint ybar).sheafFiber) :=
  sorry

/-- Comparison from the stalk of the alternative cokernel to the fibrewise
coproduct, assembled from the separated stalk formula on cover members. -/
def lowerShriekCechCokernelStalkComparison (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint ybar).sheafFiber.obj
        ((lowerShriekCechCokernelFunctor f 𝒰).obj F) ⟶
      (abelianStalkCoproduct f ybar).obj F :=
  @CategoryTheory.inv _ _ _ _
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

/-- For an open cover certified by `Fact`, the separated Čech cokernel stalk
comparison is canonically invertible. -/
instance lowerShriekCechCokernelStalkComparison_isIso_of_fact [Fact (IsOpenCover 𝒰)]
    (ybar : GeometricPoint Y) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (lowerShriekCechCokernelStalkComparison f 𝒰 ybar F) :=
  lowerShriekCechCokernelStalkComparison_isIso f 𝒰 Fact.out ybar F

/-- The comparison from separated Čech cokernel stalks to same-field stalk
coproducts is natural in the sheaf. -/
theorem lowerShriekCechCokernelStalkComparison_naturality (ybar : GeometricPoint Y)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (toSmallEtalePoint ybar).sheafFiber.map (lowerShriekCechCokernelMap f 𝒰 φ) ≫
        lowerShriekCechCokernelStalkComparison f 𝒰 ybar G =
      lowerShriekCechCokernelStalkComparison f 𝒰 ybar F ≫
        (abelianStalkCoproduct f ybar).map φ := sorry

/-- On an open covering, stalks of the separated Čech cokernel functor are
canonically the coproducts of stalks over same-field geometric lifts. -/
def lowerShriekCechCokernelStalkIso (h𝒰 : IsOpenCover 𝒰) (ybar : GeometricPoint Y) :
    lowerShriekCechCokernelFunctor f 𝒰 ⋙ (toSmallEtalePoint ybar).sheafFiber ≅
      abelianStalkCoproduct f ybar :=
  NatIso.ofComponents
    (fun F ↦ @asIso _ _ _ _ (lowerShriekCechCokernelStalkComparison f 𝒰 ybar F)
      (lowerShriekCechCokernelStalkComparison_isIso f 𝒰 h𝒰 ybar F))
    (fun φ ↦ lowerShriekCechCokernelStalkComparison_naturality f 𝒰 ybar φ)

end AlgebraicGeometry.Scheme.Etale

end
