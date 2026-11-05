/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Coproduct

/-!
# Stalk comparison for étale lower shriek versus fibrewise coproducts

If `f : X ⟶ Y` is separated and locally quasi-finite, the stalk of `f_! F` at a
geometric point `ȳ` compares with the coproduct of the stalks of `F` at
same-field geometric points of `X` over `ȳ`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology.Point
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyQuasiFinite f]
  [LocallyOfFiniteType f]
variable (ybar : GeometricPoint Y)

/-- The lift of a same-field geometric point of `X` over `ȳ` to the chosen
geometric fibre `ȳ ×_Y X`. -/
def Over.toFiber (x : Fiber f ybar) :
    Spec (.of ybar.K) ⟶ pullback ybar.hom f :=
  pullback.lift (𝟙 _) x.lift (by sorry)

/-- The structure map of `Over.toFiber` to `Spec ybar.K` is the identity. -/
theorem Over.toFiber_fst (x : Fiber f ybar) :
    Over.toFiber f ybar x ≫ pullback.fst ybar.hom f = 𝟙 _ :=
  sorry

/-- The structure map of `Over.toFiber` to `X` recovers `x.lift`. -/
theorem Over.toFiber_snd (x : Fiber f ybar) :
    Over.toFiber f ybar x ≫ pullback.snd ybar.hom f = x.lift :=
  sorry

/-- The geometric point of the fibre `ȳ ×_Y X` associated to a same-field
geometric point of `X` over `ȳ`. -/
def Over.toFiberPoint (x : Fiber f ybar) :
    GeometricPoint (pullback ybar.hom f) :=
  @GeometricPoint.of (pullback ybar.hom f) ybar.K inferInstance ybar.isAlgClosed
    (Over.toFiber f ybar x)

/-- The scheme morphism of `Over.toFiberPoint` is `Over.toFiber`. -/
theorem Over.toFiberPoint_hom (x : Fiber f ybar) :
    (Over.toFiberPoint f ybar x).hom = Over.toFiber f ybar x :=
  rfl

/-- The identity-object fibre point of `Over.toFiberPoint`. -/
def Over.toFiberLift (x : Fiber f ybar) :
    (toSmallEtalePoint (Over.toFiberPoint f ybar x)).fiber.obj
      (globalEtale (pullback ybar.hom f)) :=
  CategoryTheory.Over.homMk (Over.toFiber f ybar x)
    (by sorry)

/-- Forget the fibre factor of a lift of `toFiberPoint` to `U ×_X X_ȳ`. -/
def comapFiberToOverFiber (x : Fiber f ybar) (U : X.Etale)
    (v : (toSmallEtalePoint (Over.toFiberPoint f ybar x)).fiber.obj
      ((smallEtalePullback (pullback.snd ybar.hom f)).obj U)) :
    (toSmallEtalePoint x.point).fiber.obj U :=
  CategoryTheory.Over.homMk
    (v.left ≫ pullback.fst U.hom (pullback.snd ybar.hom f))
    (by sorry)

/-- The category of elements of the comapped fibre functor is initially small. -/
theorem initiallySmall_comap_toFiberPoint (x : Fiber f ybar) :
    InitiallySmall
      ((smallEtalePullback (pullback.snd ybar.hom f) ⋙
          (toSmallEtalePoint (Over.toFiberPoint f ybar x)).fiber).Elements) :=
  sorry

/-- Comparison of abelian étale stalks along the comap of `toFiberPoint` with the
stalk of `F` at `x̄`. -/
def comapStalkToStalk (x : Fiber f ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((toSmallEtalePoint (Over.toFiberPoint f ybar x)).comapOfMorphismOfSites
          (smallEtalePullback (pullback.snd ybar.hom f))
          (h_small := initiallySmall_comap_toFiberPoint f ybar x)).sheafFiber.obj F ⟶
      (toSmallEtalePoint x.point).sheafFiber.obj F :=
  colimit.desc _
    { pt := (toSmallEtalePoint x.point).sheafFiber.obj F
      ι :=
        { app := fun W ↦
            (toSmallEtalePoint x.point).toPresheafFiber W.unop.1
              (comapFiberToOverFiber f ybar x W.unop.1 W.unop.2) F.1
          naturality := sorry } }

/-- Inverse-image identification of the stalk of `F|_{X_ȳ}` at `toFiberPoint`
with the stalk of `F` at `x̄`. -/
def pullbackStalkToStalk (x : Fiber f ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint (Over.toFiberPoint f ybar x)).sheafFiber.obj
        (abelianPullbackAlong (pullback.snd ybar.hom f) F) ⟶
      (toSmallEtalePoint x.point).sheafFiber.obj F :=
  ((toSmallEtalePoint (Over.toFiberPoint f ybar x)).sheafFiberComapIsoOfMorphismOfSites
        (smallEtalePullback (pullback.snd ybar.hom f)) AddCommGrpCat.{u}
        (h_small := initiallySmall_comap_toFiberPoint f ybar x)).inv.app F ≫
    comapStalkToStalk f ybar x F

/-- Germ of a compactly supported global section of `F|_{X_ȳ}` at the lift of
`x̄` to the geometric fibre. -/
def compactSupportToPullbackStalk (x : Fiber f ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.of
        (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)) ⟶
      (toSmallEtalePoint (Over.toFiberPoint f ybar x)).sheafFiber.obj
        (abelianPullbackAlong (pullback.snd ybar.hom f) F) :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        (toSmallEtalePoint (Over.toFiberPoint f ybar x)).toPresheafFiber
          (globalEtale (pullback ybar.hom f)) (Over.toFiberLift f ybar x)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F).obj σ.1
      map_zero' := sorry
      map_add' := sorry }

/-- Fibrewise germ `H^0_c(X_ȳ, F|_{X_ȳ}) ⟶ F_x̄`. -/
def compactSupportGerm (x : Fiber f ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.of
        (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)) ⟶
      (toSmallEtalePoint x.point).sheafFiber.obj F :=
  compactSupportToPullbackStalk f ybar x F ≫ pullbackStalkToStalk f ybar x F

/-- The residue-field map of the geometric-fibre projection is an isomorphism,
since its finite residue-field extensions are over an algebraically closed field. -/
instance isIso_geometricFiber_residueFieldMap [LocallyQuasiFinite f]
    (z : (pullback ybar.hom f : Scheme.{u})) :
    IsIso ((pullback.fst ybar.hom f).residueFieldMap z) := by
  let p := pullback.fst ybar.hom f
  let x := p z
  letI : IsAlgClosed ybar.K := ybar.isAlgClosed
  letI : IsAlgClosed ((Spec (.of ybar.K)).residueField x) :=
    IsAlgClosed.of_ringEquiv ybar.K _
      (x.asIdeal.algEquivResidueFieldOfField.toRingEquiv.trans
        (Spec.residueFieldIso (.of ybar.K) x).commRingCatIsoToRingEquiv.symm)
  have hq : (p.residueFieldMap z).hom.QuasiFinite := by
    apply RingHom.QuasiFinite.of_comp
      (g := ((Spec (.of ybar.K)).residue x).hom)
    rw [← CommRingCat.hom_comp, residue_residueFieldMap]
    exact (RingHom.QuasiFinite.of_finite
      (RingHom.Finite.of_surjective _ ((pullback ybar.hom f).residue_surjective z))).comp
        (p.quasiFiniteAt z)
  letI := (p.residueFieldMap z).hom.toAlgebra
  haveI : Algebra.QuasiFinite ((Spec (.of ybar.K)).residueField x)
      ((pullback ybar.hom f).residueField z) := hq
  haveI : Module.Finite ((Spec (.of ybar.K)).residueField x)
      ((pullback ybar.hom f).residueField z) := .of_quasiFinite
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The structure morphism of the spectrum of a field induces an isomorphism
from the residue field of any point to the field. -/
instance isIso_specField_algebraMap (x : Spec (.of ybar.K)) :
    IsIso
      (CommRingCat.ofHom
        (algebraMap ybar.K (x.asIdeal.ResidueField : Type u))) := by
  exact x.asIdeal.algEquivResidueFieldOfField.toRingEquiv.toCommRingCatIso.isIso_hom

/-- Identify a residue field of `Spec ybar.K` with `ybar.K`. -/
def specResidueToField (x : Spec (.of ybar.K)) :
    (Spec (.of ybar.K)).residueField x ⟶ .of ybar.K :=
  (Spec.residueFieldIso (.of ybar.K) x).hom ≫
    CategoryTheory.inv
      (CommRingCat.ofHom (algebraMap ybar.K (x.asIdeal.ResidueField : Type u)))

/-- Residue-field map from a point of the geometric fibre to `ybar.K`. -/
def fiberResidueHom (z : (pullback ybar.hom f : Scheme.{u})) :
    (pullback ybar.hom f).residueField z ⟶ .of ybar.K :=
  CategoryTheory.inv ((pullback.fst ybar.hom f).residueFieldMap z) ≫
    specResidueToField ybar (pullback.fst ybar.hom f z)

/-- The same-field geometric point of `X` over `ȳ` determined by a scheme point
of the geometric fibre. -/
def overOfFiberPoint (z : (pullback ybar.hom f : Scheme.{u})) : Fiber f ybar where
  lift :=
    Spec.map (fiberResidueHom f ybar z) ≫
      (pullback ybar.hom f).fromSpecResidueField z ≫ pullback.snd ybar.hom f
  fac := by sorry

/-- The geometric fibre is locally quasi-finite over `Spec ybar.K`. -/
instance locallyQuasiFinite_geometricFiberOverField_hom [LocallyQuasiFinite f] :
    LocallyQuasiFinite (geometricFiberOverField f ybar).hom :=
  MorphismProperty.pullback_fst ybar.hom f inferInstance

/-- Reduced support of a compactly supported fibre section, as a closed
subscheme of `X_ȳ`. -/
def fiberCompactSupportSectionStructure
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
      (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :
    Scheme.ClosedSubschemeStructure
      (abelianSheafSectionSupport
        (abelianPullbackAlong (pullback.snd ybar.hom f) F)
        (globalEtale (pullback ybar.hom f)) σ.1) :=
  Scheme.ClosedSubschemeStructure.reduced _

/-- The reduced support of a compactly supported fibre section is locally
quasi-finite over `Spec ybar.K`. -/
theorem locallyQuasiFinite_fiberCompactSupportSectionStructure
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
      (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :
    LocallyQuasiFinite
      ((fiberCompactSupportSectionStructure f ybar F σ).ι ≫
        (geometricFiberOverField f ybar).hom) := by
  change LocallyQuasiFinite
    ((Scheme.IdealSheafData.vanishingIdeal
        (abelianSheafSectionSupport
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)
          (globalEtale (pullback ybar.hom f)) σ.1)).subschemeι ≫
      pullback.fst ybar.hom f)
  exact MorphismProperty.comp_mem (@LocallyQuasiFinite) _ _ inferInstance
    (MorphismProperty.pullback_fst ybar.hom f inferInstance)

/-- The reduced support of a compactly supported fibre section is quasicompact
over `Spec ybar.K`. -/
theorem quasiCompact_fiberCompactSupportSectionStructure
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
      (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :
    QuasiCompact
      ((fiberCompactSupportSectionStructure f ybar F σ).ι ≫
        (geometricFiberOverField f ybar).hom) := by
  haveI : IsProper
      ((fiberCompactSupportSectionStructure f ybar F σ).ι ≫
        (geometricFiberOverField f ybar).hom) := σ.property
  infer_instance

/-- The geometric fibre `ȳ ×_Y X` is discrete, as `f` is locally quasi-finite. -/
instance discreteTopology_geometricFiber [LocallyQuasiFinite f] :
    DiscreteTopology (pullback ybar.hom f : Scheme.{u}) := by
  letI : LocallyQuasiFinite (pullback.fst ybar.hom f) :=
    MorphismProperty.pullback_fst ybar.hom f inferInstance
  letI : IsLocallyArtinian (pullback ybar.hom f) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.fst ybar.hom f)
  infer_instance

/-- Finite set of points of the reduced support of a compactly supported fibre
section, lying over the unique point of `Spec ybar.K`. -/
def compactSupportSupportFinset
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
      (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :
    Finset (fiberCompactSupportSectionStructure f ybar F σ).subscheme :=
  (@Scheme.Hom.finite_preimage_singleton _ _
      ((fiberCompactSupportSectionStructure f ybar F σ).ι ≫
        (geometricFiberOverField f ybar).hom)
      (locallyQuasiFinite_fiberCompactSupportSectionStructure f ybar F σ)
      (quasiCompact_fiberCompactSupportSectionStructure f ybar F σ) default).toFinset

/-- The map sending a compactly supported fibre section to the finite sum of its
germs at geometric points of `X` over `ȳ`. -/
def compactSupportToCoproduct
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.of
        (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)) ⟶
      (abelianStalkCoproduct f ybar).obj F :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        ∑ z ∈ (compactSupportSupportFinset f ybar F σ).attach,
          Sigma.ι
            (fun x : Fiber f ybar ↦
              (toSmallEtalePoint x.point).sheafFiber.obj F)
            (overOfFiberPoint f ybar
              ((fiberCompactSupportSectionStructure f ybar F σ).ι z.1))
            (compactSupportGerm f ybar
              (overOfFiberPoint f ybar
                ((fiberCompactSupportSectionStructure f ybar F σ).ι z.1)) F σ)
      map_zero' := sorry
      map_add' := sorry }

/-- The germ-sum comparison `H^0_c(X_ȳ, F|_{X_ȳ}) ⟶ ⊕ F_x̄` is an isomorphism,
since `X_ȳ` is discrete with residue fields equal to `k`. -/
instance compactSupportToCoproduct_isIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (compactSupportToCoproduct f ybar F) :=
  sorry

/-- The germ-sum comparison as a bundled isomorphism `H^0_c(X_ȳ, F|_{X_ȳ}) ≅ ⊕ F_x̄`. -/
def compactSupportToCoproductIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.of
        (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)) ≅
      (abelianStalkCoproduct f ybar).obj F :=
  @asIso _ _ _ _ (compactSupportToCoproduct f ybar F)
    (compactSupportToCoproduct_isIso f ybar F)

/-- Canonical forward comparison `(f_! F)_ȳ ⟶ ⊕_{f(x̄)=ȳ} F_x̄`, as a natural
transformation in `F`. -/
def etaleLowerShriekStalkComparison :
    etaleLowerShriek f ⋙ (toSmallEtalePoint ybar).sheafFiber ⟶
      abelianStalkCoproduct f ybar where
  app F :=
    etaleLowerShriekStalkToCompactSupport f ybar F ≫
      (compactSupportToCoproductIso f ybar F).hom
  naturality := sorry

/-- Evaluating the forward comparison at an abelian étale sheaf. -/
theorem etaleLowerShriekStalkComparison_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekStalkComparison f ybar).app F =
      etaleLowerShriekStalkToCompactSupport f ybar F ≫
        (compactSupportToCoproductIso f ybar F).hom :=
  rfl

/-- The coproduct leg `F_x̄ ⟶ (f_! F)_ȳ` obtained from the coproduct inclusion,
the inverse germ-sum comparison, and the inverse compact-support comparison. -/
def etaleLowerShriekStalkι
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (x : Fiber f ybar) :
    (toSmallEtalePoint x.point).sheafFiber.obj F ⟶
      (toSmallEtalePoint ybar).sheafFiber.obj ((etaleLowerShriek f).obj F) :=
  Sigma.ι (fun x : Fiber f ybar ↦
      (toSmallEtalePoint x.point).sheafFiber.obj F) x ≫
    (compactSupportToCoproductIso f ybar F).inv ≫
      (@asIso _ _ _ _ (etaleLowerShriekStalkToCompactSupport f ybar F)
        (etaleLowerShriekStalkToCompactSupport_isIso f ybar F)).inv

/-- The canonical inverse comparison `⊕_{f(x̄)=ȳ} F_x̄ ⟶ (f_! F)_ȳ`. -/
def etaleLowerShriekStalkComparisonInv :
    abelianStalkCoproduct f ybar ⟶
      etaleLowerShriek f ⋙ (toSmallEtalePoint ybar).sheafFiber where
  app F :=
    Sigma.desc fun x : Fiber f ybar ↦ etaleLowerShriekStalkι f ybar F x
  naturality := sorry

/-- Evaluating the inverse comparison at an abelian étale sheaf. -/
theorem etaleLowerShriekStalkComparisonInv_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekStalkComparisonInv f ybar).app F =
      Sigma.desc fun x : Fiber f ybar ↦ etaleLowerShriekStalkι f ybar F x :=
  rfl

/-- The coproduct leg followed by the forward stalk comparison recovers the
coproduct inclusion of `F_x̄`. -/
theorem etaleLowerShriekStalkι_comp_iso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (x : Fiber f ybar) :
    etaleLowerShriekStalkι f ybar F x ≫
      (etaleLowerShriekStalkComparison f ybar).app F =
      Sigma.ι (fun x : Fiber f ybar ↦
        (toSmallEtalePoint x.point).sheafFiber.obj F) x :=
  sorry

section StalkIso

/-- Let `f : X ⟶ Y` be a morphism of schemes which is
separated and locally quasi-finite. Then for `F` in `Ab(X_étale)` and a
geometric point `ȳ : Spec k ⟶ Y` we have `(f_! F)_ȳ = ⊕_{f(x̄)=ȳ} F_x̄`
functorially in `F`. -/
def etaleLowerShriekStalkIso :
    etaleLowerShriek f ⋙ (toSmallEtalePoint ybar).sheafFiber ≅
      abelianStalkCoproduct f ybar where
  hom := etaleLowerShriekStalkComparison f ybar
  inv := etaleLowerShriekStalkComparisonInv f ybar
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The stalk of direct image with proper support at an abelian étale sheaf
is isomorphic to the coproduct of its stalks over the geometric fibre. -/
def etaleLowerShriekStalkIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint ybar).sheafFiber.obj ((etaleLowerShriek f).obj F) ≅
      (abelianStalkCoproduct f ybar).obj F :=
  (etaleLowerShriekStalkIso f ybar).app F

/-- The forward map of `etaleLowerShriekStalkIso` is the compact-support germ
comparison. -/
theorem etaleLowerShriekStalkIso_hom :
    (etaleLowerShriekStalkIso f ybar).hom =
      etaleLowerShriekStalkComparison f ybar :=
  rfl

/-- The inverse map of `etaleLowerShriekStalkIso` is the coproduct of the stalk
legs `etaleLowerShriekStalkι`. -/
theorem etaleLowerShriekStalkIso_inv :
    (etaleLowerShriekStalkIso f ybar).inv =
      etaleLowerShriekStalkComparisonInv f ybar :=
  rfl

end StalkIso

/-- Étale lower shriek along a separated locally quasi-finite morphism preserves
finite limits. -/
instance etaleLowerShriek_preservesFiniteLimits :
    PreservesFiniteLimits (etaleLowerShriek f) :=
  sorry

/-- Étale lower shriek along a separated locally quasi-finite morphism preserves
finite colimits. -/
instance etaleLowerShriek_preservesFiniteColimits :
    PreservesFiniteColimits (etaleLowerShriek f) :=
  sorry

/-- Let `f : X ⟶ Y` be a morphism of schemes which is
separated and locally quasi-finite. Then the functor `f_!` is exact. -/
theorem etaleLowerShriek_exact :
    exactFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (etaleLowerShriek f) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
