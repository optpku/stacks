/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Module.ULift

/-! # Universe lifting for cotangent complexes of ring sheaves -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex ComplexShape
open SheafOfModules.RingedSite
open scoped Simplicial

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.CotangentComplex.UniverseLift

/-- The topology transported to the enlarged presentation of a site. -/
abbrev siteTopology.{s, o, h} {C : Type o} [Category.{h} C] (J : GrothendieckTopology C) :
    GrothendieckTopology (AsSmall.{s + 1} C) :=
  (AsSmall.down.{h, o, s + 1}).inducedTopology J

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- The enlargement forgetful functor is an equivalence. -/
instance down_isEquivalence : (AsSmall.down.{u, u, u + 1} (C := C)).IsEquivalence :=
  inferInstanceAs ((AsSmall.equiv.{u, u, u + 1} (C := C)).inverse.IsEquivalence)

/-- The induced topology makes the enlargement a dense site presentation. -/
instance down_isDenseSubsite :
    (AsSmall.equiv.{u, u, u + 1} (C := C)).inverse.IsDenseSubsite (siteTopology.{u, u, u} J) J := by
  change (AsSmall.down.{u, u, u + 1}).IsDenseSubsite
    ((AsSmall.down.{u, u, u + 1}).inducedTopology J) J
  infer_instance

/-- Commutative-ring universe lifting preserves the sheaf condition on the enlarged site. -/
private theorem ringLift_isSheaf (B : Sheaf J CommRingCat.{u}) :
    Presheaf.IsSheaf (siteTopology.{u, u, u} J)
      ((AsSmall.down.{u, u, u + 1}).op ⋙ B.obj ⋙ CommRingCat.universeLift.{u, u + 1}) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget (siteTopology.{u, u, u} J) _
    (CategoryTheory.forget CommRingCat.{u + 1})).2
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  change Presieve.IsSheaf (siteTopology.{u, u, u} J)
    (((AsSmall.down.{u, u, u + 1}).op ⋙ B.obj ⋙ CategoryTheory.forget CommRingCat.{u}) ⋙
      CategoryTheory.uliftFunctor.{u + 1})
  rw [Presieve.isSheaf_comp_uliftFunctor_iff, ← CategoryTheory.isSheaf_iff_isSheaf_of_type]
  exact (AsSmall.equiv.{u, u, u + 1} (C := C)).inverse.op_comp_isSheaf
    (siteTopology.{u, u, u} J) J ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj B)

/-- Reindexing the site and lifting coefficient rings from universe `u` to universe `u + 1`. -/
def ringLift : Sheaf J CommRingCat.{u} ⥤ Sheaf (siteTopology.{u, u, u} J) CommRingCat.{u + 1} where
  obj B := ⟨(AsSmall.down.{u, u, u + 1}).op ⋙ B.obj ⋙ CommRingCat.universeLift.{u, u + 1},
    ringLift_isSheaf J B⟩
  map f := ObjectProperty.homMk
    ((AsSmall.down.{u, u, u + 1}).op.whiskerLeft
      (Functor.whiskerRight f.hom CommRingCat.universeLift.{u, u + 1}))
  map_id B := by ext V x; rfl
  map_comp f g := by ext V x; rfl

/-- Lifted sections carry the scalar action of the lifted coefficient ring. -/
private instance moduleSection (B : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (ringSheaf J B)) (V : (AsSmall.{u + 1} C)ᵒᵖ) :
    Module (((ringLift J).obj B).obj.obj V)
      (ULift.{u + 1} (M.val.obj ((AsSmall.down.{u, u, u + 1}).op.obj V))) :=
  inferInstanceAs (Module (ULift.{u + 1} (B.obj.obj ((AsSmall.down.{u, u, u + 1}).op.obj V)))
    (ULift.{u + 1} (M.val.obj ((AsSmall.down.{u, u, u + 1}).op.obj V))))

/-- The lifted module presheaf has the actual lifted section carriers and restriction maps. -/
private def modulePresheaf (B : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (ringSheaf J B)) :
    PresheafOfModules.{u + 1}
      (ringSheaf.{u + 1, u + 1, u + 1} (siteTopology.{u, u, u} J) ((ringLift J).obj B)).obj where
  obj V := ModuleCat.of (((ringLift J).obj B).obj.obj V)
    (ULift.{u + 1} (M.val.obj ((AsSmall.down.{u, u, u + 1}).op.obj V)))
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (((ringLift J).obj B).obj.map f).hom).obj
      (ModuleCat.of (((ringLift J).obj B).obj.obj W)
        (ULift.{u + 1} (M.val.obj ((AsSmall.down.{u, u, u + 1}).op.obj W)))))
    { toFun := fun x ↦ ULift.up (M.val.map ((AsSmall.down.{u, u, u + 1}).op.map f) x.down)
      map_add' := by intros; apply ULift.ext; exact (M.val.map _).hom.map_add _ _
      map_smul' := by intros; apply ULift.ext; exact M.val.map_smul _ _ _ }
  map_id V := by
    ext x
    apply ULift.ext
    exact congrArg (fun k ↦ k.hom x.down) (M.val.map_id _)
  map_comp f g := by
    ext x
    apply ULift.ext
    simpa only [Functor.map_comp] using! M.val.map_comp_apply
      ((AsSmall.down.{u, u, u + 1}).op.map f) ((AsSmall.down.{u, u, u + 1}).op.map g) x.down

/-- The lifted additive presheaf is a sheaf because reindexing and additive universe lifting preserve sheaves. -/
private theorem modulePresheaf_isSheaf (B : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} (ringSheaf J B)) :
    Presheaf.IsSheaf (siteTopology.{u, u, u} J) (modulePresheaf J B M).presheaf := by
  let N : Sheaf (siteTopology.{u, u, u} J) AddCommGrpCat.{u} :=
    ((AsSmall.equiv.{u, u, u + 1} (C := C)).sheafCongr J (siteTopology.{u, u, u} J) AddCommGrpCat.{u}).functor.obj
      ⟨M.val.presheaf, M.isSheaf⟩
  exact Presheaf.isSheaf_comp_of_isSheaf (siteTopology.{u, u, u} J) N.obj
    AddCommGrpCat.uliftFunctor.{u + 1, u} N.property

/-- The coefficient-universe lift of module sheaves uses the ordinary `ULift` on sections. -/
def moduleLift (B : Sheaf J CommRingCat.{u}) :
    SheafOfModules.{u} (ringSheaf J B) ⥤
      SheafOfModules.{u + 1}
        (ringSheaf.{u + 1, u + 1, u + 1} (siteTopology.{u, u, u} J) ((ringLift J).obj B)) where
  obj M := ⟨modulePresheaf J B M, modulePresheaf_isSheaf J B M⟩
  map f :=
    { val :=
        { app := fun V ↦ ModuleCat.ofHom
            { toFun := fun x ↦ ULift.up (f.val.app _ x.down)
              map_add' := by intros; apply ULift.ext; exact (f.val.app _).hom.map_add _ _
              map_smul' := by intros; apply ULift.ext; exact (f.val.app _).hom.map_smul _ _ }
          naturality := by
            intro V W g
            ext x
            apply ULift.ext
            exact PresheafOfModules.naturality_apply f.val
              ((AsSmall.down.{u, u, u + 1}).op.map g) x.down } }
  map_id M := by ext V x; rfl
  map_comp f g := by ext V x; rfl

/-- Module universe lifting preserves addition of morphisms. -/
instance moduleLift_additive (B : Sheaf J CommRingCat.{u}) : (moduleLift J B).Additive where
  map_add := by intros; ext V x; apply ULift.ext; rfl

/-- Evaluation sends each enlarged-site generator to the native generator of the same section. -/
private def freeCompare (A : Sheaf J CommRingCat.{u})
    (B : Under A) :
    CategoryTheory.Sheaf.FreeAlgebra.Presentation.obj ((ringLift J).obj A)
        ((Under.post (ringLift J)).obj B) ⟶
      (Under.post (ringLift J)).obj (CategoryTheory.Sheaf.FreeAlgebra.Presentation.obj A B) :=
  CategoryTheory.Sheaf.FreeAlgebra.evaluation
    ((Under.post (ringLift J)).obj (CategoryTheory.Sheaf.FreeAlgebra.Presentation.obj A B)) _
    (ObjectProperty.homMk
      ((AsSmall.down.{u, u, u + 1}).op.whiskerLeft
        (Functor.whiskerRight (CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A B).hom
          CategoryTheory.uliftFunctor.{u + 1})))

/-- Reindexing identifies the free algebra on the lifted section generators. -/
private theorem freeCompare_isIso (A : Sheaf J CommRingCat.{u})
    (B : Under A) : IsIso (freeCompare J A B) := sorry

/-- The enlarged free-algebra comonad endofunctor. -/
private abbrev enlargedFree (A : Sheaf J CommRingCat.{u}) :=
  (SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction
    ((ringLift J).obj A)).toComonad.toFunctor

/-- Iterated free-algebra comparison starts at the identity and evaluates lifted generators. -/
private def resolutionIter (A : Sheaf J CommRingCat.{u})
    (B : Under A) : (k : ℕ) →
    ((Endofunctor.iterate (enlargedFree J A) k).obj ((Under.post (ringLift J)).obj B) ⟶
      (Under.post (ringLift J)).obj ((Endofunctor.iterate ((freeForgetAdjunction A).toComonad.toFunctor) k).obj B)) :=
  Nat.rec (𝟙 _) (fun k cmp ↦
    (enlargedFree J A).map cmp ≫
      freeCompare J A ((Endofunctor.iterate ((freeForgetAdjunction A).toComonad.toFunctor) k).obj B))

/-- Standard-resolution terms compare by the recursively evaluated free generators. -/
private def resolutionCompare (A : Sheaf J CommRingCat.{u})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :
    SheafOfModules.RingedSite.CotangentComplex.standardTerm ((ringLift J).obj A)
        ((Under.post (ringLift J)).obj B) n ⟶
      (Under.post (ringLift J)).obj (standardTerm A B n) :=
  eqToHom (Comonad.simplicialResolution.eval.degree
    (SheafOfModules.RingedSite.CotangentComplex.freeForgetAdjunction
      ((ringLift J).obj A)).toComonad ((Under.post (ringLift J)).obj B) n.unop.len) ≫
    resolutionIter J A B (n.unop.len + 1) ≫
      (Under.post (ringLift J)).map
        (eqToHom (Comonad.simplicialResolution.eval.degree
          (freeForgetAdjunction A).toComonad B n.unop.len).symm)

/-- Resolution comparison preserves augmentations and every simplicial operator. -/
private theorem resolutionCompare_laws
    (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (∀ n, (resolutionCompare J A B n).right ≫
      (ringLift J).map (standardAugmentation A B n) =
        SheafOfModules.RingedSite.CotangentComplex.standardAugmentation
          ((ringLift J).obj A) ((Under.post (ringLift J)).obj B) n) ∧
    (∀ {n m} (f : n ⟶ m),
      (SheafOfModules.RingedSite.CotangentComplex.standardMap
        ((ringLift J).obj A) ((Under.post (ringLift J)).obj B) f).right ≫
          (resolutionCompare J A B m).right =
        (resolutionCompare J A B n).right ≫ (ringLift J).map (standardMap A B f).right) := sorry

/-- The homogeneous standard-resolution term on the enlarged site. -/
private abbrev enlargedTerm (A : Sheaf J CommRingCat.{u})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :=
  SheafOfModules.RingedSite.CotangentComplex.standardTerm ((ringLift J).obj A)
    ((Under.post (ringLift J)).obj B) n

/-- Native differentials reindexed on the enlarged site and restricted along resolution comparison. -/
private abbrev differentialTarget (A : Sheaf J CommRingCat.{u})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :=
  (restrictionAlong (resolutionCompare J A B n).right).obj
    ((moduleLift J (standardTerm A B n).right).obj
      (relativeDifferentials.{u, u, u} (standardTerm A B n).hom))

/-- The additive differential assignment sends `q` to the native differential of its resolution image. -/
private def differentialValue (A : Sheaf J CommRingCat.{u})
    (B : Under A) (n : SimplexCategoryᵒᵖ)
    (V : (AsSmall.{u + 1} C)ᵒᵖ) :
    (enlargedTerm J A B n).right.obj.obj V →+ (differentialTarget J A B n).val.obj V :=
  { toFun := fun q ↦ ULift.up
      ((relativeDifferential.{u, u, u} (standardTerm A B n).hom).d
        (((resolutionCompare J A B n).right.hom.app V q).down))
    map_zero' := by
      apply ULift.ext
      rw [map_zero]
      exact (relativeDifferential.{u, u, u} (standardTerm A B n).hom).d.map_zero
    map_add' := by
      intro q r
      apply ULift.ext
      rw [map_add]
      exact (relativeDifferential.{u, u, u} (standardTerm A B n).hom).d.map_add
          (((resolutionCompare J A B n).right.hom.app V q).down)
          (((resolutionCompare J A B n).right.hom.app V r).down) }

/-- The lifted native differential satisfies the Leibniz, restriction, and relative-base laws. -/
private theorem differentialsCompare_laws
    (A : Sheaf J CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    (∀ V (a b : (enlargedTerm J A B n).right.obj.obj V),
      differentialValue J A B n V (a * b) =
        a • differentialValue J A B n V b + b • differentialValue J A B n V a) ∧
    (∀ {V W} (f : V ⟶ W) (a : (enlargedTerm J A B n).right.obj.obj V),
      differentialValue J A B n W ((enlargedTerm J A B n).right.obj.map f a) =
        (differentialTarget J A B n).val.map f (differentialValue J A B n V a)) ∧
    (∀ V (a : ((ringLift J).obj A).obj.obj V),
      differentialValue J A B n V ((enlargedTerm J A B n).hom.hom.app V a) = 0) := sorry

/-- Universal descent of the native differential composed with resolution comparison. -/
private def differentialsCompare (A : Sheaf J CommRingCat.{u})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials.{u + 1, u + 1, u + 1} (enlargedTerm J A B n).hom ⟶
      differentialTarget J A B n :=
  relativeDifferentialDesc.{u + 1, u + 1, u + 1} (enlargedTerm J A B n).hom
    { d := fun {V} ↦ differentialValue J A B n V
      d_mul := (differentialsCompare_laws J A B n).1 _
      d_map := (differentialsCompare_laws J A B n).2.1
      d_app := (differentialsCompare_laws J A B n).2.2 _ }

/-- The augmentation of the homogeneous enlarged resolution. -/
private abbrev enlargedAugmentation (A : Sheaf J CommRingCat.{u})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :=
  SheafOfModules.RingedSite.CotangentComplex.standardAugmentation
    ((ringLift J).obj A) ((Under.post (ringLift J)).obj B) n

/-- The native extension-of-scalars unit for a standard-resolution term. -/
private abbrev nativeTensorUnit (A : Sheaf J CommRingCat.{u})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :=
  (ChangeOfRings.extendRestrictAdjunction.{u}
    (ringSheafMap.{u, u, u} (standardAugmentation A B n))).unit.app
      (relativeDifferentials.{u, u, u} (standardTerm A B n).hom)

/-- The native scalar-extension unit, reindexed and restricted through resolution comparison. -/
private def tensorUnitCompare (A : Sheaf J CommRingCat.{u})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :
    differentialTarget J A B n ⟶
      (restrictionAlong (enlargedAugmentation J A B n)).obj
        ((moduleLift J B.right).obj ((simplicialModule A B).obj n)) where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (X := (differentialTarget J A B n).val.obj V)
        (Y := ((restrictionAlong (enlargedAugmentation J A B n)).obj
          ((moduleLift J B.right).obj ((simplicialModule A B).obj n))).val.obj V)
        { toFun := fun x ↦ ULift.up ((nativeTensorUnit J A B n).val.app
            ((AsSmall.down.{u, u, u + 1}).op.obj V) x.down)
          map_add' := by intros; apply ULift.ext; exact ((nativeTensorUnit J A B n).val.app _).hom.map_add _ _
          map_smul' := by
            intro r x
            apply ULift.ext
            have h := congrArg (fun f ↦ ((f.hom.app V).hom r).down)
              ((resolutionCompare_laws J A B).1 n)
            have linear := ((nativeTensorUnit J A B n).val.app
              ((AsSmall.down.{u, u, u + 1}).op.obj V)).hom.map_smul
                (((resolutionCompare J A B n).right.hom.app V).hom r).down x.down
            exact linear.trans (congrArg
              (fun b : (ringSheaf J B.right).obj.obj ((AsSmall.down.{u, u, u + 1}).op.obj V) ↦
                @SMul.smul _ (((simplicialModule A B).obj n).val.obj
                  ((AsSmall.down.{u, u, u + 1}).op.obj V)) inferInstance b
                    ((nativeTensorUnit J A B n).val.app _ x.down)) h) }
      naturality := by
        intro V W f
        ext x
        apply ULift.ext
        exact congrArg (fun g ↦ g.hom x.down)
          ((nativeTensorUnit J A B n).val.naturality
            ((AsSmall.down.{u, u, u + 1}).op.map f)) }

/-- Scalar extension of the differential comparison by its genuine adjunction. -/
private def tensorCompare (A : Sheaf J CommRingCat.{u})
    (B : Under A) (n : SimplexCategoryᵒᵖ) :
    (SheafOfModules.RingedSite.CotangentComplex.simplicialModule.{u + 1}
      ((ringLift J).obj A) ((Under.post (ringLift J)).obj B)).obj n ⟶
      (moduleLift J B.right).obj ((simplicialModule A B).obj n) :=
  ((SheafOfModules.ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap.{u + 1, u + 1, u + 1} (enlargedAugmentation J A B n))).homEquiv
      (relativeDifferentials.{u + 1, u + 1, u + 1} (enlargedTerm J A B n).hom)
      ((moduleLift J B.right).obj ((simplicialModule A B).obj n))).symm
      (differentialsCompare J A B n ≫ tensorUnitCompare J A B n)

/-- The scalar-extended differential comparisons commute with all simplicial operators. -/
private theorem tensorCompare_naturality
    (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (SheafOfModules.RingedSite.CotangentComplex.simplicialModule.{u + 1}
      ((ringLift J).obj A) ((Under.post (ringLift J)).obj B)).map f ≫
        tensorCompare J A B m =
      tensorCompare J A B n ≫ (moduleLift J B.right).map
        ((simplicialModule A B).map f) := sorry

/-- The source cotangent cochain complex reindexed and lifted in coefficients. -/
private abbrev reindexedCochain {A B : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) :=
  ((moduleLift J B).mapHomologicalComplex (up ℤ)).obj (CotangentComplex.obj A (Under.mk φ))

/-- In nonpositive degrees, cotangent comparison is scalar-extended universal differentiation. -/
private def negativeComponent {A B : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (n : ℕ) :
    (SheafOfModules.RingedSite.CotangentComplex.obj ((ringLift J).obj A)
      (Under.mk ((ringLift J).map φ))).X (-n) ⟶ (reindexedCochain J φ).X (-n) :=
  (SheafOfModules.RingedSite.CotangentComplex.objXIso ((ringLift J).obj A)
    (Under.mk ((ringLift J).map φ)) n).hom ≫
      tensorCompare J A (Under.mk φ) (op ⦋n⦌) ≫
        (moduleLift J B).map (CotangentComplex.objXIso A (Under.mk φ) n).inv

/-- Cotangent comparison uses the resolution comparison in nonpositive degrees and zero otherwise. -/
private def comparisonComponent {A B : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (i : ℤ) :
    (SheafOfModules.RingedSite.CotangentComplex.obj ((ringLift J).obj A)
      (Under.mk ((ringLift J).map φ))).X i ⟶ (reindexedCochain J φ).X i :=
  match i with
  | Int.ofNat 0 => negativeComponent J φ 0
  | Int.ofNat (n + 1) => 0
  | Int.negSucc n => negativeComponent J φ (n + 1)

/-- Cotangent comparison commutes with the cochain differentials. -/
private theorem comparison_comm {A B : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    comparisonComponent J φ i ≫ (reindexedCochain J φ).d i j =
      (SheafOfModules.RingedSite.CotangentComplex.obj ((ringLift J).obj A)
        (Under.mk ((ringLift J).map φ))).d i j ≫ comparisonComponent J φ j := sorry

/-- The enlarged homogeneous cotangent complex maps canonically to the lifted native complex. -/
def comparison {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    SheafOfModules.RingedSite.CotangentComplex.obj ((ringLift J).obj A)
        (Under.mk ((ringLift J).map φ)) ⟶
      ((moduleLift J B).mapHomologicalComplex (up ℤ)).obj
        (CotangentComplex.obj A (Under.mk φ)) where
  f := comparisonComponent J φ
  comm' := comparison_comm J φ

/-- The canonical comparison with the lifted native cotangent complex is invertible. -/
instance comparison_isIso {A B : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) : IsIso (comparison J φ) := sorry

/-- Enlarging a site while lifting coefficients identifies its cotangent complexes. -/
def iso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    SheafOfModules.RingedSite.CotangentComplex.obj ((ringLift J).obj A)
        (Under.mk ((ringLift J).map φ)) ≅
      ((moduleLift J B).mapHomologicalComplex (up ℤ)).obj
        (CotangentComplex.obj A (Under.mk φ)) :=
  asIso (comparison J φ)

/-- The forward map of the site transport is its canonical comparison. -/
theorem iso_hom {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (iso J φ).hom = comparison J φ := rfl

end SheafOfModules.RingedSite.CotangentComplex.UniverseLift
