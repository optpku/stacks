/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import stacks_project.Chap63.Lemma_63_3_11_Comparison
public import stacks_project.Chap63.Lemma_63_4_2_StalkCoproduct

/-!
# Stalk comparison for étale lower shriek versus fibrewise coproducts

If `f : X ⟶ Y` is separated and locally quasi-finite, the stalk of `f_! F` at a
geometric point `ȳ` compares with the coproduct of the stalks of `F` at
same-field geometric points of `X` over `ȳ`.
-/

@[expose] public section

open CategoryTheory hiding Over
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

/-- The commutativity witness for the pullback lift of a same-field geometric
point of `X` over `ȳ` into the geometric fibre `ȳ ×_Y X`. -/
theorem Over.toFiber_condition (x : Over f ybar) :
    𝟙 (Spec (.of ybar.K)) ≫ ybar.hom = x.toScheme ≫ f :=
  sorry

/-- The lift of a same-field geometric point of `X` over `ȳ` to the chosen
geometric fibre `ȳ ×_Y X`. -/
def Over.toFiber (x : Over f ybar) :
    Spec (.of ybar.K) ⟶ pullback ybar.hom f :=
  pullback.lift (𝟙 _) x.toScheme (Over.toFiber_condition f ybar x)

/-- The structure map of `Over.toFiber` to `Spec ybar.K` is the identity. -/
theorem Over.toFiber_fst (x : Over f ybar) :
    Over.toFiber f ybar x ≫ pullback.fst ybar.hom f = 𝟙 _ :=
  sorry

/-- The structure map of `Over.toFiber` to `X` recovers `x.toScheme`. -/
theorem Over.toFiber_snd (x : Over f ybar) :
    Over.toFiber f ybar x ≫ pullback.snd ybar.hom f = x.toScheme :=
  sorry

/-- The geometric point of the fibre `ȳ ×_Y X` associated to a same-field
geometric point of `X` over `ȳ`. -/
def Over.toFiberPoint (x : Over f ybar) :
    GeometricPoint (pullback ybar.hom f) :=
  @GeometricPoint.of (pullback ybar.hom f) ybar.K inferInstance ybar.isAlgClosed
    (Over.toFiber f ybar x)

/-- The scheme morphism of `Over.toFiberPoint` is `Over.toFiber`. -/
theorem Over.toFiberPoint_hom (x : Over f ybar) :
    (Over.toFiberPoint f ybar x).hom = Over.toFiber f ybar x :=
  rfl

/-- The unique lift of `Over.toFiberPoint` to the identity étale object of the
geometric fibre. -/
theorem Over.toFiberLift_fac (x : Over f ybar) :
    Over.toFiber f ybar x ≫ (globalEtale (pullback ybar.hom f)).hom =
      (Over.toFiberPoint f ybar x).hom :=
  sorry

/-- The identity-object fibre point of `Over.toFiberPoint`. -/
def Over.toFiberLift (x : Over f ybar) :
    (toSmallEtalePoint (Over.toFiberPoint f ybar x)).fiber.obj
      (globalEtale (pullback ybar.hom f)) :=
  CategoryTheory.Over.homMk (Over.toFiber f ybar x)
    (Over.toFiberLift_fac f ybar x)

/-- The pairing of a lift of `toFiberPoint` to `U ×_X X_ȳ` with the projection
to `U` is a lift of `x` to `U`. -/
theorem comapFiberToOverFiber_fac (x : Over f ybar) (U : X.Etale)
    (v : (toSmallEtalePoint (Over.toFiberPoint f ybar x)).fiber.obj
      ((smallEtalePullback (pullback.snd ybar.hom f)).obj U)) :
    v.left ≫ pullback.fst U.hom (pullback.snd ybar.hom f) ≫ U.hom = x.toScheme :=
  sorry

/-- Forget the fibre factor of a lift of `toFiberPoint` to `U ×_X X_ȳ`. -/
def comapFiberToOverFiber (x : Over f ybar) (U : X.Etale)
    (v : (toSmallEtalePoint (Over.toFiberPoint f ybar x)).fiber.obj
      ((smallEtalePullback (pullback.snd ybar.hom f)).obj U)) :
    (toSmallEtalePoint x.toGeometricPoint).fiber.obj U :=
  CategoryTheory.Over.homMk
    (v.left ≫ pullback.fst U.hom (pullback.snd ybar.hom f))
    (comapFiberToOverFiber_fac f ybar x U v)

/-- The category of elements of the comapped fibre functor is initially small. -/
instance initiallySmall_comap_toFiberPoint (x : Over f ybar) :
    InitiallySmall
      ((smallEtalePullback (pullback.snd ybar.hom f) ⋙
          (toSmallEtalePoint (Over.toFiberPoint f ybar x)).fiber).Elements) :=
  sorry

/-- Comparison of abelian étale stalks along the comap of `toFiberPoint` with the
stalk of `F` at `x̄`. -/
def comapStalkToStalk (x : Over f ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((toSmallEtalePoint (Over.toFiberPoint f ybar x)).comapOfMorphismOfSites
          (smallEtalePullback (pullback.snd ybar.hom f))).sheafFiber.obj F ⟶
      (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F :=
  colimit.desc _
    { pt := (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F
      ι :=
        { app := fun W ↦
            (toSmallEtalePoint x.toGeometricPoint).toPresheafFiber W.unop.1
              (comapFiberToOverFiber f ybar x W.unop.1 W.unop.2) F.1
          naturality := sorry } }

/-- Inverse-image identification of the stalk of `F|_{X_ȳ}` at `toFiberPoint`
with the stalk of `F` at `x̄`. -/
def pullbackStalkToStalk (x : Over f ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint (Over.toFiberPoint f ybar x)).sheafFiber.obj
        (abelianPullbackAlong (pullback.snd ybar.hom f) F) ⟶
      (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F :=
  ((toSmallEtalePoint (Over.toFiberPoint f ybar x)).sheafFiberComapIsoOfMorphismOfSites
        (smallEtalePullback (pullback.snd ybar.hom f)) AddCommGrpCat.{u}).inv.app F ≫
    comapStalkToStalk f ybar x F

/-- Germ of a compactly supported global section of `F|_{X_ȳ}` at the lift of
`x̄` to the geometric fibre. -/
def compactSupportToPullbackStalk (x : Over f ybar)
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
def compactSupportGerm (x : Over f ybar)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.of
        (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)) ⟶
      (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F :=
  compactSupportToPullbackStalk f ybar x F ≫ pullbackStalkToStalk f ybar x F

/-- The residue-field map of the geometric-fibre projection is an isomorphism,
since residue fields on `X_ȳ` equal `ybar.K`. -/
instance isIso_geometricFiber_residueFieldMap
    (z : (pullback ybar.hom f : Scheme.{u})) :
    IsIso ((pullback.fst ybar.hom f).residueFieldMap z) :=
  sorry

/-- The structure morphism of the spectrum of a field induces an isomorphism
from the residue field of any point to the field. -/
instance isIso_specField_algebraMap (x : Spec (.of ybar.K)) :
    IsIso
      (CommRingCat.ofHom
        (algebraMap ybar.K (x.asIdeal.ResidueField : Type u))) :=
  sorry

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

/-- The scheme morphism associated to `overOfFiberPoint` lies over `ȳ`. -/
theorem overOfFiberPoint_fac (z : (pullback ybar.hom f : Scheme.{u})) :
    (Spec.map (fiberResidueHom f ybar z) ≫
          (pullback ybar.hom f).fromSpecResidueField z ≫
            pullback.snd ybar.hom f) ≫
        f =
      ybar.hom :=
  sorry

/-- The same-field geometric point of `X` over `ȳ` determined by a scheme point
of the geometric fibre. -/
def overOfFiberPoint (z : (pullback ybar.hom f : Scheme.{u})) : Over f ybar where
  toScheme :=
    Spec.map (fiberResidueHom f ybar z) ≫
      (pullback ybar.hom f).fromSpecResidueField z ≫ pullback.snd ybar.hom f
  fac := overOfFiberPoint_fac f ybar z

/-- The geometric fibre is locally quasi-finite over `Spec ybar.K`. -/
instance locallyQuasiFinite_geometricFiberOverField_hom :
    LocallyQuasiFinite (geometricFiberOverField f ybar).hom :=
  sorry

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
instance locallyQuasiFinite_fiberCompactSupportSectionStructure
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
      (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :
    LocallyQuasiFinite
      ((fiberCompactSupportSectionStructure f ybar F σ).ι ≫
        (geometricFiberOverField f ybar).hom) :=
  sorry

/-- The reduced support of a compactly supported fibre section is quasicompact
over `Spec ybar.K`. -/
instance quasiCompact_fiberCompactSupportSectionStructure
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
      (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :
    QuasiCompact
      ((fiberCompactSupportSectionStructure f ybar F σ).ι ≫
        (geometricFiberOverField f ybar).hom) :=
  sorry

/-- The geometric fibre `ȳ ×_Y X` is discrete, as `f` is locally quasi-finite and
locally of finite type. -/
instance discreteTopology_geometricFiber :
    DiscreteTopology (pullback ybar.hom f : Scheme.{u}) :=
  sorry

/-- Classical decidable equality on same-field geometric points over `ȳ`. -/
noncomputable instance (priority := low) decidableEq_over :
    DecidableEq (Over f ybar) :=
  Classical.decEq _

/-- Finite set of points of the reduced support of a compactly supported fibre
section, lying over the unique point of `Spec ybar.K`. -/
def compactSupportSupportFinset
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
      (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :
    Finset (fiberCompactSupportSectionStructure f ybar F σ).subscheme :=
  (((fiberCompactSupportSectionStructure f ybar F σ).ι ≫
          (geometricFiberOverField f ybar).hom).finite_preimage_singleton
      default).toFinset

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
            (fun x : Over f ybar ↦
              (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F)
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
the inverse germ-sum comparison, and the inverse compact-support comparison of
Lemma 63.3.11. -/
def etaleLowerShriekStalkι
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (x : Over f ybar) :
    (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F ⟶
      (toSmallEtalePoint ybar).sheafFiber.obj ((etaleLowerShriek f).obj F) :=
  Sigma.ι (fun x : Over f ybar ↦
      (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F) x ≫
    (compactSupportToCoproductIso f ybar F).inv ≫
      (@asIso _ _ _ _ (etaleLowerShriekStalkToCompactSupport f ybar F)
        (etaleLowerShriekStalkToCompactSupport_isIso f ybar F)).inv

/-- The canonical inverse comparison `⊕_{f(x̄)=ȳ} F_x̄ ⟶ (f_! F)_ȳ`. -/
def etaleLowerShriekStalkComparisonInv :
    abelianStalkCoproduct f ybar ⟶
      etaleLowerShriek f ⋙ (toSmallEtalePoint ybar).sheafFiber where
  app F :=
    Sigma.desc fun x : Over f ybar ↦ etaleLowerShriekStalkι f ybar F x
  naturality := sorry

/-- Evaluating the inverse comparison at an abelian étale sheaf. -/
theorem etaleLowerShriekStalkComparisonInv_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekStalkComparisonInv f ybar).app F =
      Sigma.desc fun x : Over f ybar ↦ etaleLowerShriekStalkι f ybar F x :=
  rfl

/-- The coproduct leg followed by the forward stalk comparison recovers the
coproduct inclusion of `F_x̄`. -/
theorem etaleLowerShriekStalkι_comp_iso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (x : Over f ybar) :
    etaleLowerShriekStalkι f ybar F x ≫
      (etaleLowerShriekStalkComparison f ybar).app F =
      Sigma.ι (fun x : Over f ybar ↦
        (toSmallEtalePoint x.toGeometricPoint).sheafFiber.obj F) x :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
