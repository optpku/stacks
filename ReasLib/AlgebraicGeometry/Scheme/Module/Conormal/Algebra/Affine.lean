module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Affine
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Functoriality

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry

/-- The kernel of the section map from an affine open of a scheme to its inverse image along
a scheme morphism.  For a closed affine immersion chart, this is its defining ideal. -/
abbrev immersionAffineConormalIdeal
    {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) : Ideal (Γ(X, U)) :=
  RingHom.ker (i.app U).hom

/-- The associated graded ring of the sectionwise kernel ideal on an affine chart. -/
abbrev immersionAffineConormalAlgebra
    {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) : Type u :=
  Ideal.AssociatedGraded.ring (immersionAffineConormalIdeal i U)

namespace Scheme.Hom.Conormal

variable {R : Type u} [CommRing R] (I : Ideal R)

set_option maxHeartbeats 4000000 in
/-- The canonical degreewise map from the associated graded ring of an ideal to the global
sections of the conormal algebra of the corresponding quotient morphism. -/
noncomputable def quotientMapAssociatedGradedToSections (n : ℕ) :
    ModuleCat.of (R ⧸ I) (Ideal.AssociatedGraded.grade I n) ⟶
      (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).obj
        ((Scheme.ConormalAlgebra
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj n) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let α := RingedSpace.Hom.inverseImageStructureSheafHomComm q.toShHom
  let W : (Opens (Spec (CommRingCat.of R)))ᵒᵖ := Opposite.op ⊤
  let V : (Opens (Spec (CommRingCat.of (R ⧸ I))))ᵒᵖ := Opposite.op ⊤
  let F : CommRingCat.of R ⟶
      ((TopCat.Sheaf.pullback CommRingCat.{u} q.toShHom.hom.base).obj
        (Spec (CommRingCat.of R)).sheaf).obj.obj V :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (((TopCat.Sheaf.pullbackPushforwardAdjunction
        CommRingCat.{u} q.toShHom.hom.base).unit.app
        (Spec (CommRingCat.of R)).sheaf).hom.app W)
  let G : CommRingCat.of (R ⧸ I) ⟶
      (Spec (CommRingCat.of (R ⧸ I))).sheaf.obj.obj V :=
    (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv
  let A := (TopCat.Sheaf.pullback CommRingCat.{u} q.toShHom.hom.base).obj
    (Spec (CommRingCat.of R)).sheaf
  let J := KernelIdeal.sectionIdeal α V
  let source : ModuleCat (R ⧸ I) :=
    ModuleCat.of (R ⧸ I) (Ideal.AssociatedGraded.grade I n)
  let target : ModuleCat (R ⧸ I) :=
    (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).obj
      ((Scheme.ConormalAlgebra q).obj n)
  let targetR : ModuleCat R :=
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj target
  let P := KernelIdeal.AssociatedGraded.presheaf.{u, u} α n
  let sectionsNative : ModuleCat
      ((Spec (CommRingCat.of (R ⧸ I))).sheaf.obj.obj V) :=
    ((Scheme.ConormalAlgebra q).obj n).val.obj V
  let AF : R →+* (Spec (CommRingCat.of (R ⧸ I))).sheaf.obj.obj V :=
    (α.hom.app V).hom.comp F.hom
  let sectionsR : ModuleCat R :=
    (ModuleCat.restrictScalars AF).obj sectionsNative
  have hF (r : R) : α.hom.app V (F r) = G (Ideal.Quotient.mk I r) := by
    have hs :
        (TopCat.Sheaf.pullbackPushforwardAdjunction
              CommRingCat.{u} q.toShHom.hom.base).unit.app
              (Spec (CommRingCat.of R)).sheaf ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} q.toShHom.hom.base).map α =
          RingedSpace.Hom.commRingSheafPushforwardMap q.toShHom := by
      simpa only [Functor.id_obj, Adjunction.homEquiv_unit,
        RingedSpace.Hom.inverseImageStructureSheafHomComm, α] using
        (Equiv.apply_symm_apply
          ((TopCat.Sheaf.pullbackPushforwardAdjunction
            CommRingCat.{u} q.toShHom.hom.base).homEquiv
            (Spec (CommRingCat.of R)).sheaf
            (Spec (CommRingCat.of (R ⧸ I))).sheaf)
          (RingedSpace.Hom.commRingSheafPushforwardMap q.toShHom))
    have hsW := congrArg (fun f ↦ f.hom.app W) hs
    change
      (((TopCat.Sheaf.pullbackPushforwardAdjunction
        CommRingCat.{u} q.toShHom.hom.base).unit.app
        (Spec (CommRingCat.of R)).sheaf).hom.app W) ≫ α.hom.app V = q.appTop at hsW
    have hsF : F ≫ α.hom.app V =
        CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ G := by
      dsimp only [F, G]
      rw [Category.assoc, hsW]
      exact
        (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (Ideal.Quotient.mk I))).symm
    exact ConcreteCategory.congr_hom hsF r
  have map_mem_pow (k : ℕ) {x : R} (hx : x ∈ I ^ k) : F.hom x ∈ J ^ k := by
    have hx' : F.hom x ∈ Ideal.map F.hom (I ^ k) :=
      Ideal.mem_map_of_mem F.hom hx
    rw [Ideal.map_pow] at hx'
    exact (pow_le_pow_left'
      ((Ideal.map_le_iff_le_comap).2 (quotientMapIdeal_le_conormalIdeal I)) k) hx'
  have map_mem_stage (k : ℕ) {x : R}
      (hx : x ∈ Ideal.AssociatedGraded.stage I R k) :
      F.hom x ∈ Ideal.AssociatedGraded.stage J (A.obj.obj V) k := by
    change x ∈ Ideal.PowerSubmodule.stage I R k at hx
    change F.hom x ∈ Ideal.PowerSubmodule.stage J (A.obj.obj V) k
    rw [Ideal.PowerSubmodule.stage_regular] at hx ⊢
    exact map_mem_pow k hx
  let stageMap : Ideal.AssociatedGraded.stage I R n →ₛₗ[F.hom]
      Ideal.AssociatedGraded.stage J (A.obj.obj V) n :=
    { toFun := fun x ↦
        ⟨F.hom (x : R), map_mem_stage n x.2⟩
      map_add' := fun (x y : Ideal.AssociatedGraded.stage I R n) ↦
        Subtype.ext (map_add F.hom (x : R) (y : R))
      map_smul' := fun (r : R) (x : Ideal.AssociatedGraded.stage I R n) ↦
        Subtype.ext (map_mul F.hom r (x : R)) }
  let pieceMap : Ideal.AssociatedGraded.piece I R n →ₛₗ[F.hom]
      Ideal.AssociatedGraded.piece J (A.obj.obj V) n :=
    (Ideal.AssociatedGraded.denominator I R n).mapQ
      (Ideal.AssociatedGraded.denominator J (A.obj.obj V) n) stageMap (by
        intro x hx
        change F.hom (x : R) ∈
          Ideal.AssociatedGraded.stage J (A.obj.obj V) (n + 1)
        exact map_mem_stage (n + 1) hx)
  let mapped : Ideal.AssociatedGraded.grade I n →ₛₗ[F.hom]
      Ideal.AssociatedGraded.grade J n :=
    { toFun := fun x ↦ (Ideal.AssociatedGraded.gradeEquivPiece J n).symm
        (pieceMap (Ideal.AssociatedGraded.gradeEquivPiece I n x))
      map_add' := by
        intro x y
        simp only [map_add]
      map_smul' := by
        intro r x
        simp only [map_smul, map_smulₛₗ] }
  let extendUnit :
      ModuleCat.of (A.obj.obj V) (Ideal.AssociatedGraded.grade J n) ⟶
        (ModuleCat.restrictScalars (α.hom.app V).hom).obj (P.obj V) :=
    (ModuleCat.extendRestrictScalarsAdj (α.hom.app V).hom).unit.app
      (ModuleCat.of (A.obj.obj V) (Ideal.AssociatedGraded.grade J n))
  let η : P.obj V ⟶ sectionsNative :=
    (moduleSheafificationUnitToVal
      (Spec (CommRingCat.of (R ⧸ I))).sheaf P).app V
  let liftedR : Ideal.AssociatedGraded.grade I n →ₗ[R] sectionsR :=
    { toFun := fun x ↦ η.hom (extendUnit.hom (mapped x))
      map_add' := by
        intro x y
        simp only [map_add]
      map_smul' := by
        intro r x
        change η.hom (extendUnit.hom (mapped (r • x))) =
          AF r • η.hom (extendUnit.hom (mapped x))
        rw [map_smulₛₗ, map_smul]
        change η.hom (α.hom.app V (F r) • extendUnit.hom (mapped x)) =
          AF r • η.hom (extendUnit.hom (mapped x))
        rw [map_smul]
        rfl }
  let sectionsToTarget : sectionsR ⟶ targetR :=
    ModuleCat.homMk (𝟙 _) (fun r ↦ by
      have hr : target.smul (Ideal.Quotient.mk I r) =
          sectionsNative.smul (AF r) := by
        change sectionsNative.smul (G (Ideal.Quotient.mk I r)) =
          sectionsNative.smul (α.hom.app V (F r))
        rw [hF]
      rw [Category.id_comp, Category.comp_id]
      exact hr)
  let liftedTargetR : Ideal.AssociatedGraded.grade I n →ₗ[R] targetR :=
    sectionsToTarget.hom.comp liftedR
  exact ModuleCat.homMk
    (AddCommGrpCat.ofHom liftedTargetR.toAddMonoidHom) (fun s ↦ by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
      ext x
      change (target.smul (Ideal.Quotient.mk I r)).hom (liftedTargetR x) =
        liftedTargetR ((source.smul (Ideal.Quotient.mk I r)).hom x)
      rw [show (source.smul (Ideal.Quotient.mk I r)).hom x =
          r • (show Ideal.AssociatedGraded.grade I n from x) by
        change (Ideal.Quotient.mk I r) •
            (show Ideal.AssociatedGraded.grade I n from x) =
          r • (show Ideal.AssociatedGraded.grade I n from x)
        exact IsScalarTower.algebraMap_smul (A := R ⧸ I) r
          (show Ideal.AssociatedGraded.grade I n from x)]
      exact (liftedTargetR.map_smul r x).symm)

/-- On a homogeneous stage representative, the affine comparison agrees with the canonical
successive-quotient presentation of that homogeneous class. -/
theorem quotientMapAssociatedGradedToSections_stageClass (n : ℕ)
    (x : Ideal.AssociatedGraded.stage I R n) :
    quotientMapAssociatedGradedToSections I n
        (Ideal.AssociatedGraded.stageClassLinear I n x) =
      quotientMapAssociatedGradedToSections I n
        ((Ideal.AssociatedGraded.gradeEquivPiece I n).symm
          (Submodule.Quotient.mk x)) := sorry

/-- The affine comparison carries the degree-zero unit of the associated graded ring to the
degree-zero unit section of the conormal algebra. -/
theorem quotientMapAssociatedGradedToSections_one :
    quotientMapAssociatedGradedToSections I 0
        (⟨1, SetLike.one_mem_graded (Ideal.AssociatedGraded.grade I)⟩ :
          Ideal.AssociatedGraded.grade I 0) =
      (Scheme.ConormalAlgebra
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).one
          (Opposite.op ⊤) := sorry

/-- The affine comparison preserves multiplication of homogeneous associated-graded
classes. -/
theorem quotientMapAssociatedGradedToSections_mul (n m : ℕ)
    (x : Ideal.AssociatedGraded.grade I n)
    (y : Ideal.AssociatedGraded.grade I m) :
    quotientMapAssociatedGradedToSections I (n + m)
        ⟨(x : Ideal.AssociatedGraded.ring I) *
            (y : Ideal.AssociatedGraded.ring I),
          SetLike.mul_mem_graded x.2 y.2⟩ =
      (Scheme.ConormalAlgebra
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mul
          (Opposite.op ⊤) n m
          (quotientMapAssociatedGradedToSections I n x)
          (quotientMapAssociatedGradedToSections I m y) := sorry

/-- In every degree, the canonical affine comparison from an ideal's associated graded ring
to the global sections of the quotient conormal algebra is an isomorphism. -/
theorem quotientMapAssociatedGradedToSections_isIso (n : ℕ) :
    IsIso (quotientMapAssociatedGradedToSections I n) := sorry

end Scheme.Hom.Conormal

namespace Scheme.ConormalAlgebra

variable {X Z : Scheme.{u}}

/-- An affine chart for a morphism has affine inverse image and a surjective map on sections. -/
def IsAffineChart (i : Z ⟶ X) (U : X.affineOpens) : Prop :=
  IsAffineOpen (i ⁻¹ᵁ (U : X.Opens)) ∧
    Function.Surjective (i.app (U : X.Opens))

/-- The ring homomorphism from sections on an open to sections of the pulled-back structure
sheaf on its inverse image. -/
noncomputable def affinePullbackRingMap (i : Z ⟶ X) (U : X.affineOpens) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i.base).unit.app
    X.sheaf).hom.app (Opposite.op (U : X.Opens))).hom

/-- Composing the pullback unit on sections with the inverse-image structure map recovers the
usual map on sections induced by the scheme morphism. -/
theorem affinePullbackRingMap_comp (i : Z ⟶ X) (U : X.affineOpens) :
    ((RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom).hom.app
      (Opposite.op (i ⁻¹ᵁ (U : X.Opens)))).hom.comp
        (affinePullbackRingMap i U) =
      (i.app (U : X.Opens)).hom := sorry

/-- The pullback-unit ring map carries the affine kernel ideal into the sectionwise kernel ideal
of the inverse-image structure morphism. -/
theorem affinePullbackConormalIdeal_le_comap (i : Z ⟶ X) (U : X.affineOpens) :
    immersionAffineConormalIdeal i (U : X.Opens) ≤
      Ideal.comap (affinePullbackRingMap i U)
        (KernelIdeal.sectionIdeal
          (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)
          (Opposite.op (i ⁻¹ᵁ (U : X.Opens)))) := sorry

/-- The canonical degreewise map from an affine associated-graded class to the corresponding
section of the conormal algebra on the inverse-image open. -/
noncomputable def affineGradeToSections (i : Z ⟶ X) (U : X.affineOpens) (n : ℕ) :
    Ideal.AssociatedGraded.grade
        (immersionAffineConormalIdeal i (U : X.Opens)) n →+
      ((Scheme.ConormalAlgebra i).obj n).val.obj
        (Opposite.op (i ⁻¹ᵁ (U : X.Opens))) := by
  let α := RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom
  let V : (Z.Opens)ᵒᵖ := Opposite.op (i ⁻¹ᵁ (U : X.Opens))
  let source : ModuleCat (X.presheaf.obj (Opposite.op (U : X.Opens))) :=
    ModuleCat.of (X.presheaf.obj (Opposite.op (U : X.Opens)))
      (Ideal.AssociatedGraded.grade
        (immersionAffineConormalIdeal i (U : X.Opens)) n)
  let target : ModuleCat
      (((TopCat.Sheaf.pullback CommRingCat.{u} i.base).obj X.sheaf).obj.obj V) :=
    KernelIdeal.AssociatedGraded.gradeObj α n V
  let gradeLinear : source →ₛₗ[affinePullbackRingMap i U] target :=
    Ideal.AssociatedGraded.mapGradeLinear (affinePullbackRingMap i U)
      (affinePullbackConormalIdeal_le_comap i U) n
  let gradeMap := ModuleCat.semilinearMapAddEquiv
    (affinePullbackRingMap i U) source target gradeLinear
  let extendUnit :=
    (ModuleCat.extendRestrictScalarsAdj (α.hom.app V).hom).unit.app
      target
  let sheafificationUnit :=
    (moduleSheafificationUnitToVal Z.sheaf
      (KernelIdeal.AssociatedGraded.presheaf.{u, u} α n)).app V
  exact sheafificationUnit.hom.toAddMonoidHom.comp
    (extendUnit.hom.toAddMonoidHom.comp gradeMap.hom.toAddMonoidHom)

/-- On an affine closed chart, the canonical degreewise map identifies the associated graded
piece with the sections of the conormal algebra. -/
theorem affineGradeToSections_bijective (i : Z ⟶ X) (U : X.affineOpens)
    (hU : IsAffineChart i U) (n : ℕ) :
    Function.Bijective (affineGradeToSections i U n) := sorry

end Scheme.ConormalAlgebra

end AlgebraicGeometry
