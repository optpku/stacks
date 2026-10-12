/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Module
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Associated graded algebra sheaves of kernel ideals

For a morphism of commutative ring sheaves on one site, this file forms the sectionwise
associated graded modules of its kernel ideal, extends scalars to the target ring sheaf, and
sheafifies.  The sectionwise unit and multiplication induce a commutative naturally graded
algebra sheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
open scoped TensorProduct

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.KernelIdeal.AssociatedGraded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {A O₂ : Sheaf J CommRingCat.{max u v}}

/-- The degree-`n` homogeneous section module of the associated graded ring of the
sectionwise kernel ideal. -/
abbrev gradeObj (pi : A ⟶ O₂) (n : ℕ) (U : Cᵒᵖ) :
    ModuleCat.{max u v} (A.obj.obj U) :=
  ModuleCat.of (A.obj.obj U)
    (Ideal.AssociatedGraded.grade (KernelIdeal.sectionIdeal pi U) n)

/-- Restriction of sections carries one sectionwise kernel ideal into the next. -/
theorem sectionIdeal_le_comap (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) :
    KernelIdeal.sectionIdeal pi U ≤
      Ideal.comap (A.obj.map f).hom (KernelIdeal.sectionIdeal pi V) := by
  simpa only [KernelIdeal.sections_eq_sectionIdeal] using
    IdealSheaf.sections_le_comap (KernelIdeal.subobject pi) f

/-- The map on homogeneous kernel-ideal grades induced by restriction of sections. -/
noncomputable def mapGrade (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ)
    (x : gradeObj pi n U) : gradeObj pi n V :=
  Ideal.AssociatedGraded.mapGrade
    (KernelIdeal.sectionIdeal pi U) (KernelIdeal.sectionIdeal pi V)
    (A.obj.map f).hom (sectionIdeal_le_comap pi f) n x

/-- Restriction on homogeneous kernel-ideal grades preserves addition. -/
theorem mapGrade_add (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ)
    (x y : gradeObj pi n U) :
    mapGrade pi f n (x + y) = mapGrade pi f n x + mapGrade pi f n y := sorry

/-- Restriction on homogeneous kernel-ideal grades is semilinear over restriction of rings. -/
theorem mapGrade_smul (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ)
    (r : A.obj.obj U) (x : gradeObj pi n U) :
    mapGrade pi f n (r • x) = A.obj.map f r • mapGrade pi f n x := sorry

/-- Restriction on homogeneous kernel-ideal grades as a semilinear map. -/
noncomputable def mapGradeSemilinear (pi : A ⟶ O₂) {U V : Cᵒᵖ}
    (f : U ⟶ V) (n : ℕ) :
    gradeObj pi n U →ₛₗ[(A.obj.map f).hom] gradeObj pi n V where
  toFun := mapGrade pi f n
  map_add' := mapGrade_add pi f n
  map_smul' := mapGrade_smul pi f n

/-- Restriction on homogeneous kernel-ideal grades as a morphism into a restriction of
scalars. -/
noncomputable def mapGradeHom (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ) :
    gradeObj pi n U ⟶
      (ModuleCat.restrictScalars (A.obj.map f).hom).obj (gradeObj pi n V) :=
  ModuleCat.semilinearMapAddEquiv (A.obj.map f).hom
    (gradeObj pi n U) (gradeObj pi n V) (mapGradeSemilinear pi f n)

/-- The degree-`n` scalar extension of the sectionwise homogeneous grade to the target
section ring. -/
noncomputable abbrev obj (pi : A ⟶ O₂) (n : ℕ) (U : Cᵒᵖ) :
    ModuleCat.{max u v} (O₂.obj.obj U) :=
  (ModuleCat.extendScalars (pi.hom.app U).hom).obj (gradeObj pi n U)

/-- Naturality of the ring-sheaf morphism, expressed as equality of composite ring
homomorphisms. -/
theorem ringSquare (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (pi.hom.app V).hom.comp (A.obj.map f).hom =
      (O₂.obj.map f).hom.comp (pi.hom.app U).hom := by
  exact congrArg CommRingCat.Hom.hom (pi.hom.naturality f)

/-- The adjoint form of restriction on scalar-extended homogeneous grades. -/
noncomputable def restrictionAdjoint (pi : A ⟶ O₂) {U V : Cᵒᵖ}
    (f : U ⟶ V) (n : ℕ) :
    gradeObj pi n U ⟶
      (ModuleCat.restrictScalars (pi.hom.app U).hom).obj
        ((ModuleCat.restrictScalars (O₂.obj.map f).hom).obj (obj pi n V)) :=
  mapGradeHom pi f n ≫
    (ModuleCat.restrictScalars (A.obj.map f).hom).map
      ((ModuleCat.extendRestrictScalarsAdj (pi.hom.app V).hom).unit.app
        (gradeObj pi n V)) ≫
    (ModuleCat.restrictScalarsComp (A.obj.map f).hom (pi.hom.app V).hom).inv.app _ ≫
    (ModuleCat.restrictScalarsCongr (ringSquare pi f)).hom.app _ ≫
    (ModuleCat.restrictScalarsComp (pi.hom.app U).hom (O₂.obj.map f).hom).hom.app _

/-- Restriction on scalar-extended homogeneous grades. -/
noncomputable def restriction (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ) :
    obj pi n U ⟶
      (ModuleCat.restrictScalars (O₂.obj.map f).hom).obj (obj pi n V) :=
  ((ModuleCat.extendRestrictScalarsAdj (pi.hom.app U).hom).homEquiv _ _).symm
    (restrictionAdjoint pi f n)

/-- Restriction on scalar-extended grades respects identity morphisms. -/
theorem restriction_id (pi : A ⟶ O₂) (U : Cᵒᵖ) (n : ℕ) :
    restriction pi (𝟙 U) n =
      (ModuleCat.restrictScalarsId' (O₂.obj.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (O₂.obj.map_id U))).inv.app _ := sorry

/-- Restriction on scalar-extended grades respects composition. -/
theorem restriction_comp (pi : A ⟶ O₂) {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (n : ℕ) :
    restriction pi (f ≫ g) n =
      restriction pi f n ≫
        (ModuleCat.restrictScalars (O₂.obj.map f).hom).map (restriction pi g n) ≫
        (ModuleCat.restrictScalarsComp' (O₂.obj.map f).hom (O₂.obj.map g).hom
          (O₂.obj.map (f ≫ g)).hom
          (congrArg CommRingCat.Hom.hom (O₂.obj.map_comp f g))).inv.app _ := sorry

/-- The presheaf of scalar-extended degree-`n` homogeneous kernel-ideal grades. -/
noncomputable def presheaf (pi : A ⟶ O₂) (n : ℕ) :
    PresheafOfModules (ringSheaf J O₂).obj where
  obj U := obj pi n U
  map f := restriction pi f n
  map_id U := restriction_id pi U n
  map_comp f g := restriction_comp pi f g n

/-- Evaluation of the homogeneous-grade presheaf. -/
theorem presheaf_obj (pi : A ⟶ O₂) (n : ℕ) (U : Cᵒᵖ) :
    (presheaf pi n).obj U = obj pi n U := sorry

/-- The scalar extension of the successive quotient `I ^ n / I ^ (n + 1)` on an object of
the site. -/
noncomputable abbrev pieceObj (pi : A ⟶ O₂) (n : ℕ) (U : Cᵒᵖ) :
    ModuleCat.{max u v} (O₂.obj.obj U) :=
  (ModuleCat.extendScalars (pi.hom.app U).hom).obj
    (ModuleCat.of (A.obj.obj U)
      (Ideal.AssociatedGraded.piece (KernelIdeal.sectionIdeal pi U) (A.obj.obj U) n))

/-- The objectwise comparison between a homogeneous grade and its successive ideal-power
quotient after scalar extension. -/
noncomputable def gradePieceObjIso (pi : A ⟶ O₂) (n : ℕ) (U : Cᵒᵖ) :
    obj pi n U ≅ pieceObj pi n U :=
  (ModuleCat.extendScalars (pi.hom.app U).hom).mapIso
    (Ideal.AssociatedGraded.gradeEquivPiece
      (KernelIdeal.sectionIdeal pi U) n).toModuleIso

/-- Restriction on successive ideal-power quotient pieces, transported through the canonical
homogeneous-grade comparison. -/
noncomputable def pieceRestriction (pi : A ⟶ O₂) {U V : Cᵒᵖ}
    (f : U ⟶ V) (n : ℕ) :
    pieceObj pi n U ⟶
      (ModuleCat.restrictScalars (O₂.obj.map f).hom).obj (pieceObj pi n V) :=
  (gradePieceObjIso pi n U).inv ≫ restriction pi f n ≫
    (ModuleCat.restrictScalars (O₂.obj.map f).hom).map
      (gradePieceObjIso pi n V).hom

/-- The transported quotient-piece restriction respects identity morphisms. -/
theorem pieceRestriction_id (pi : A ⟶ O₂) (U : Cᵒᵖ) (n : ℕ) :
    pieceRestriction pi (𝟙 U) n =
      (ModuleCat.restrictScalarsId' (O₂.obj.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom (O₂.obj.map_id U))).inv.app _ := by
  rw [pieceRestriction, restriction_id]
  erw [← ModuleCat.restrictScalarsId'App_inv_naturality
    (O₂.obj.map (𝟙 U)).hom
    (congrArg CommRingCat.Hom.hom (O₂.obj.map_id U))]
  simp only [Iso.inv_hom_id_assoc]
  ext x
  rfl

/-- The transported quotient-piece restriction respects composition. -/
theorem pieceRestriction_comp (pi : A ⟶ O₂) {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (n : ℕ) :
    pieceRestriction pi (f ≫ g) n =
      pieceRestriction pi f n ≫
        (ModuleCat.restrictScalars (O₂.obj.map f).hom).map (pieceRestriction pi g n) ≫
        (ModuleCat.restrictScalarsComp' (O₂.obj.map f).hom (O₂.obj.map g).hom
          (O₂.obj.map (f ≫ g)).hom
          (congrArg CommRingCat.Hom.hom (O₂.obj.map_comp f g))).inv.app _ := by
  simp only [pieceRestriction, restriction_comp]
  ext x
  simp

/-- The presheaf of scalar-extended successive kernel-ideal quotient pieces. -/
noncomputable def piecePresheaf (pi : A ⟶ O₂) (n : ℕ) :
    PresheafOfModules (ringSheaf J O₂).obj where
  obj U := pieceObj pi n U
  map f := pieceRestriction pi f n
  map_id U := pieceRestriction_id pi U n
  map_comp f g := pieceRestriction_comp pi f g n

/-- The objectwise grade-to-quotient comparison commutes with restriction. -/
theorem gradePieceIso_naturality (pi : A ⟶ O₂) (n : ℕ) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    restriction pi f n ≫
        (ModuleCat.restrictScalars (O₂.obj.map f).hom).map
          (gradePieceObjIso pi n V).hom =
      (gradePieceObjIso pi n U).hom ≫ pieceRestriction pi f n := sorry

/-- The presheaf-level isomorphism between homogeneous grades and successive ideal-power
quotients. -/
noncomputable def gradePiecePresheafIso (pi : A ⟶ O₂) (n : ℕ) :
    presheaf pi n ≅ piecePresheaf pi n :=
  PresheafOfModules.isoMk (fun U ↦ gradePieceObjIso pi n U)
    (fun {_ _} f ↦ gradePieceIso_naturality pi n f)

/-- The degree-`n` module sheaf obtained by sheafifying homogeneous kernel-ideal grades. -/
noncomputable abbrev sheaf (pi : A ⟶ O₂) (n : ℕ) :
    ringedSiteModuleCategory J O₂ :=
  (moduleSheafification O₂).obj (presheaf pi n)

/-- The sheafification of the scalar-extended successive kernel-ideal quotient pieces. -/
noncomputable abbrev pieceSheaf (pi : A ⟶ O₂) (n : ℕ) :
    ringedSiteModuleCategory J O₂ :=
  (moduleSheafification O₂).obj (piecePresheaf pi n)

/-- A sheafified homogeneous grade is canonically the sheafification of the corresponding
scalar-extended quotient `I ^ n / I ^ (n + 1)`. -/
noncomputable def gradePieceSheafIso (pi : A ⟶ O₂) (n : ℕ) :
    sheaf pi n ≅ pieceSheaf pi n :=
  (moduleSheafification O₂).mapIso (gradePiecePresheafIso pi n)

/-- Bilinear multiplication between two homogeneous grades of an associated graded ring. -/
noncomputable def gradeMulLinear
    {R : Type w} [CommRing R] (I : Ideal R) (n m : ℕ) :
    Ideal.AssociatedGraded.grade I n →ₗ[R]
      Ideal.AssociatedGraded.grade I m →ₗ[R]
        Ideal.AssociatedGraded.grade I (n + m) where
  toFun x :=
    { toFun := fun y ↦ ⟨(x : Ideal.AssociatedGraded.ring I) * y,
          SetLike.mul_mem_graded x.2 y.2⟩
      map_add' := by
        intro y z
        ext
        exact mul_add _ _ _
      map_smul' := by
        intro r y
        apply Subtype.ext
        change (x : Ideal.AssociatedGraded.ring I) *
            (r • (y : Ideal.AssociatedGraded.ring I)) =
          r •
            ((x : Ideal.AssociatedGraded.ring I) *
            (y : Ideal.AssociatedGraded.ring I))
        exact Algebra.mul_smul_comm r _ _ }
  map_add' x y := LinearMap.ext fun z ↦ Subtype.ext <| by
    change ((x : Ideal.AssociatedGraded.ring I) +
        (y : Ideal.AssociatedGraded.ring I)) *
        (z : Ideal.AssociatedGraded.ring I) =
      (x : Ideal.AssociatedGraded.ring I) *
          (z : Ideal.AssociatedGraded.ring I) +
        (y : Ideal.AssociatedGraded.ring I) *
          (z : Ideal.AssociatedGraded.ring I)
    exact add_mul _ _ _
  map_smul' r x := LinearMap.ext fun y ↦ Subtype.ext <| by
    change (r • (x : Ideal.AssociatedGraded.ring I)) *
          (y : Ideal.AssociatedGraded.ring I) =
      r •
        ((x : Ideal.AssociatedGraded.ring I) *
        (y : Ideal.AssociatedGraded.ring I))
    exact Algebra.smul_mul_assoc r _ _

/-- Multiplication of homogeneous grades as a morphism out of their tensor product. -/
noncomputable def gradeMulHom
    {R : Type w} [CommRing R] (I : Ideal R) (n m : ℕ) :
    tensorObj
        (ModuleCat.of R (Ideal.AssociatedGraded.grade I n))
        (ModuleCat.of R (Ideal.AssociatedGraded.grade I m)) ⟶
      ModuleCat.of R (Ideal.AssociatedGraded.grade I (n + m)) :=
  ModuleCat.ofHom (TensorProduct.lift (gradeMulLinear I n m))

/-- The scalar-ring map into the degree-zero homogeneous grade. -/
noncomputable def gradeOneLinear
    {R : Type w} [CommRing R] (I : Ideal R) :
    R →ₗ[R] Ideal.AssociatedGraded.grade I 0 where
  toFun r := r •
    (⟨1, SetLike.one_mem_graded (Ideal.AssociatedGraded.grade I)⟩ :
      Ideal.AssociatedGraded.grade I 0)
  map_add' r s := by rw [add_smul]
  map_smul' r s := by
    change (r * s) •
        (⟨1, SetLike.one_mem_graded (Ideal.AssociatedGraded.grade I)⟩ :
          Ideal.AssociatedGraded.grade I 0) =
      r • s •
        (⟨1, SetLike.one_mem_graded (Ideal.AssociatedGraded.grade I)⟩ :
          Ideal.AssociatedGraded.grade I 0)
    exact mul_smul r s _

/-- The scalar-ring map into degree zero as a morphism of modules. -/
noncomputable def gradeOneHom
    {R : Type w} [CommRing R] (I : Ideal R) :
    𝟙_ (ModuleCat.{w} R) ⟶
      ModuleCat.of R (Ideal.AssociatedGraded.grade I 0) :=
  ModuleCat.ofHom (gradeOneLinear I)

/-- Objectwise multiplication after extending homogeneous grades to the target section ring. -/
noncomputable def mulObj (pi : A ⟶ O₂) (U : Cᵒᵖ) (n m : ℕ) :
    tensorObj (obj pi n U) (obj pi m U) ⟶ obj pi (n + m) U :=
  μ (ModuleCat.extendScalars (pi.hom.app U).hom)
      (gradeObj pi n U) (gradeObj pi m U) ≫
    (ModuleCat.extendScalars (pi.hom.app U).hom).map
      (gradeMulHom (KernelIdeal.sectionIdeal pi U) n m)

/-- Objectwise degree-zero unit after extending the homogeneous grade to the target section
ring. -/
noncomputable def oneObj (pi : A ⟶ O₂) (U : Cᵒᵖ) :
    𝟙_ (ModuleCat.{max u v} (O₂.obj.obj U)) ⟶ obj pi 0 U :=
  ε (ModuleCat.extendScalars (pi.hom.app U).hom) ≫
    (ModuleCat.extendScalars (pi.hom.app U).hom).map
      (gradeOneHom (KernelIdeal.sectionIdeal pi U))

/-- Objectwise degree-zero units commute with restriction. -/
theorem one_naturality (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (𝟙_ (PresheafOfModules (ringSheaf J O₂).obj)).map f ≫
        (ModuleCat.restrictScalars (O₂.obj.map f).hom).map (oneObj pi V) =
      oneObj pi U ≫ restriction pi f 0 := sorry

/-- Objectwise homogeneous multiplication commutes with restriction. -/
theorem mul_naturality (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) (n m : ℕ) :
    (PresheafOfModules.Monoidal.tensorObj (presheaf pi n) (presheaf pi m)).map f ≫
        (ModuleCat.restrictScalars (O₂.obj.map f).hom).map (mulObj pi V n m) =
      mulObj pi U n m ≫ restriction pi f (n + m) := sorry

/-- The degree-zero unit morphism of the associated-graded module presheaves. -/
noncomputable def oneHom (pi : A ⟶ O₂) :
    𝟙_ (PresheafOfModules (ringSheaf J O₂).obj) ⟶ presheaf pi 0 where
  app U := oneObj pi U
  naturality f := one_naturality pi f

/-- The multiplication morphism between two degrees of the associated-graded module
presheaves. -/
noncomputable def mulHom (pi : A ⟶ O₂) (n m : ℕ) :
    PresheafOfModules.Monoidal.tensorObj (presheaf pi n) (presheaf pi m) ⟶
      presheaf pi (n + m) where
  app U := mulObj pi U n m
  naturality f := mul_naturality pi f n m

/-- The degree-zero unit morphism after module sheafification. -/
noncomputable def one (pi : A ⟶ O₂) : unitModule J O₂ ⟶ sheaf pi 0 :=
  (moduleSheafificationValIso O₂ (unitModule J O₂)).inv ≫
    (moduleSheafification O₂).map (oneHom pi)

/-- Multiplication between two degrees after module sheafification. -/
noncomputable def mul (pi : A ⟶ O₂) (n m : ℕ) :
    tensorObj (sheaf pi n) (sheaf pi m) ⟶ sheaf pi (n + m) :=
  (ModuleSheafification.tensorIso O₂ (presheaf pi n) (presheaf pi m)).hom ≫
    (moduleSheafification O₂).map (mulHom pi n m)

/-- The degree-zero unit as a local section of the associated-graded algebra sheaf. -/
noncomputable def oneSection (pi : A ⟶ O₂) (U : Cᵒᵖ) :
    (sheaf pi 0).val.obj U :=
  ((one pi).val.app U).hom (1 : O₂.obj.obj U)

/-- Multiplication of two homogeneous local sections in the sheafified associated graded
algebra. -/
noncomputable def mulSection (pi : A ⟶ O₂) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf pi n).val.obj U) (y : (sheaf pi m).val.obj U) :
    (sheaf pi (n + m)).val.obj U :=
  ((mul pi n m).val.app U).hom (tensorSection O₂ U x y)

/-- Homogeneous local multiplication is additive in its right argument. -/
theorem mulSection_add_right (pi : A ⟶ O₂) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf pi n).val.obj U) (y y' : (sheaf pi m).val.obj U) :
    mulSection pi U n m x (y + y') =
      mulSection pi U n m x y + mulSection pi U n m x y' := sorry

/-- Homogeneous local multiplication is linear in its right argument. -/
theorem mulSection_smul_right (pi : A ⟶ O₂) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf pi n).val.obj U) (r : O₂.obj.obj U)
    (y : (sheaf pi m).val.obj U) :
    mulSection pi U n m x (r • y) =
      (RingHom.id (O₂.obj.obj U)) r • mulSection pi U n m x y := sorry

/-- Right-linear multiplication by a fixed homogeneous local section. -/
noncomputable def mulSectionRight (pi : A ⟶ O₂) (U : Cᵒᵖ) (n m : ℕ)
    (x : (sheaf pi n).val.obj U) :
    (sheaf pi m).val.obj U →ₗ[O₂.obj.obj U] (sheaf pi (n + m)).val.obj U where
  toFun := mulSection pi U n m x
  map_add' := mulSection_add_right pi U n m x
  map_smul' := mulSection_smul_right pi U n m x

/-- Right-linear homogeneous multiplication is additive in its fixed left argument. -/
theorem mulSectionRight_add (pi : A ⟶ O₂) (U : Cᵒᵖ) (n m : ℕ)
    (x x' : (sheaf pi n).val.obj U) :
    mulSectionRight pi U n m (x + x') =
      mulSectionRight pi U n m x + mulSectionRight pi U n m x' := sorry

/-- Right-linear homogeneous multiplication is linear in its fixed left argument. -/
theorem mulSectionRight_smul (pi : A ⟶ O₂) (U : Cᵒᵖ) (n m : ℕ)
    (r : O₂.obj.obj U) (x : (sheaf pi n).val.obj U) :
    mulSectionRight pi U n m (r • x) =
      r • mulSectionRight pi U n m x := sorry

/-- Bilinear multiplication on local sections of two homogeneous degrees. -/
noncomputable def mulSectionLinear (pi : A ⟶ O₂) (U : Cᵒᵖ) (n m : ℕ) :
    (sheaf pi n).val.obj U →ₗ[O₂.obj.obj U]
      (sheaf pi m).val.obj U →ₗ[O₂.obj.obj U]
        (sheaf pi (n + m)).val.obj U where
  toFun := mulSectionRight pi U n m
  map_add' := mulSectionRight_add pi U n m
  map_smul' := mulSectionRight_smul pi U n m

/-- The degree-zero unit section commutes with restriction. -/
theorem oneSection_map (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((sheaf pi 0).val.map f).hom (oneSection pi U) = oneSection pi V := sorry

/-- Homogeneous local multiplication commutes with restriction. -/
theorem mulSection_map (pi : A ⟶ O₂) {U V : Cᵒᵖ} (f : U ⟶ V)
    (n m : ℕ) (x : (sheaf pi n).val.obj U) (y : (sheaf pi m).val.obj U) :
    ((sheaf pi (n + m)).val.map f).hom (mulSection pi U n m x y) =
      mulSection pi V n m
        (((sheaf pi n).val.map f).hom x)
        (((sheaf pi m).val.map f).hom y) := sorry

/-- Homogeneous local multiplication is associative. -/
theorem mulSection_assoc (pi : A ⟶ O₂) (U : Cᵒᵖ) (i j k : ℕ)
    (a : (sheaf pi i).val.obj U) (b : (sheaf pi j).val.obj U)
    (c : (sheaf pi k).val.obj U) :
    HEq (mulSection pi U (i + j) k (mulSection pi U i j a b) c)
      (mulSection pi U i (j + k) a (mulSection pi U j k b c)) := sorry

/-- The degree-zero local section is a left unit. -/
theorem oneSection_mul (pi : A ⟶ O₂) (U : Cᵒᵖ) (n : ℕ)
    (a : (sheaf pi n).val.obj U) :
    HEq (mulSection pi U 0 n (oneSection pi U) a) a := sorry

/-- The degree-zero local section is a right unit. -/
theorem mulSection_one (pi : A ⟶ O₂) (U : Cᵒᵖ) (n : ℕ)
    (a : (sheaf pi n).val.obj U) :
    HEq (mulSection pi U n 0 a (oneSection pi U)) a := sorry

/-- Homogeneous local multiplication is commutative. -/
theorem mulSection_comm (pi : A ⟶ O₂) (U : Cᵒᵖ) (n m : ℕ)
    (a : (sheaf pi n).val.obj U) (b : (sheaf pi m).val.obj U) :
    HEq (mulSection pi U n m a b) (mulSection pi U m n b a) := sorry

/-- The sheafified associated graded of a kernel ideal as a naturally graded algebra sheaf. -/
noncomputable def algebra (pi : A ⟶ O₂) : GradedAlgebraSheaf O₂ ℕ where
  obj := sheaf pi
  one := oneSection pi
  mul := mulSectionLinear pi
  map_one := oneSection_map pi
  map_mul := mulSection_map pi
  mul_assoc := mulSection_assoc pi
  one_mul := oneSection_mul pi
  mul_one := mulSection_one pi

/-- The degree-`n` object of the kernel associated graded algebra is the sheafification of the
scalar-extended homogeneous grade. -/
theorem algebra_obj (pi : A ⟶ O₂) (n : ℕ) :
    (algebra pi).obj n = sheaf pi n := sorry

/-- The kernel associated graded algebra sheaf is ordinarily commutative. -/
instance algebra_isCommutative (pi : A ⟶ O₂) : (algebra pi).IsCommutative where
  mul_comm := mulSection_comm pi

end SheafOfModules.RingedSite.KernelIdeal.AssociatedGraded
