module

public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.KernelAnnihilation
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Scalar descent along thickenings

A module annihilated by the kernel of a thickening's structure map admits scalar descent
by locally lifting scalars and gluing their actions on the underlying additive sheaf.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.privateInPublic true

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ScalarDescent

variable {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsThickening i]
variable (M : X'.Modules)
variable (hM : SheafOfModules.IsAnnihilatedByKernel (toRingCatSheafHom i) M)

private def localActionFamily (U : Opens X')
    (r : X.presheaf.obj (op ((Opens.map i.hom.base).obj U))) (m : M.val.obj (op U)) :
    (Presheaf.imageSieve i.hom.c r).arrows.FamilyOfElements
      (M.val.presheaf ⋙ forget AddCommGrpCat) :=
  fun V inclusion member =>
    @SMul.smul (X'.ringCatSheaf.obj.obj (op V)) (M.val.obj (op V)) inferInstance
      (Presheaf.localPreimage i.hom.c r inclusion member)
      (M.val.map inclusion.op m)

include hM in
private theorem localAction_compatible (U : Opens X')
    (r : X.presheaf.obj (op ((Opens.map i.hom.base).obj U))) (m : M.val.obj (op U)) :
    (localActionFamily i M U r m).Compatible := by
  intro V₁ V₂ W restriction₁ restriction₂ inclusion₁ inclusion₂ member₁ member₂ square
  change M.val.map restriction₁.op
      (@SMul.smul (X'.ringCatSheaf.obj.obj (op V₁)) (M.val.obj (op V₁)) inferInstance
        (Presheaf.localPreimage i.hom.c r inclusion₁ member₁) (M.val.map inclusion₁.op m)) =
    M.val.map restriction₂.op
      (@SMul.smul (X'.ringCatSheaf.obj.obj (op V₂)) (M.val.obj (op V₂)) inferInstance
        (Presheaf.localPreimage i.hom.c r inclusion₂ member₂) (M.val.map inclusion₂.op m))
  erw [M.val.map_smul, M.val.map_smul,
    ← M.val.map_comp_apply, ← M.val.map_comp_apply]
  simp only [← op_comp]
  apply eq_of_sub_eq_zero
  erw [← sub_smul]
  apply hM
  change i.hom.c.app (op W)
    (X'.presheaf.map restriction₁.op (Presheaf.localPreimage i.hom.c r inclusion₁ member₁) -
      X'.presheaf.map restriction₂.op (Presheaf.localPreimage i.hom.c r inclusion₂ member₂)) = 0
  rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply,
    Presheaf.app_localPreimage, Presheaf.app_localPreimage]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, square, sub_self]

/-- The action of a reduced scalar on a section is obtained by gluing the actions of its
local lifts. -/
def act (U : Opens X')
    (r : X.presheaf.obj (op ((Opens.map i.hom.base).obj U))) (m : M.val.obj (op U)) :
    M.val.obj (op U) :=
  (Presheaf.IsSheaf.isSheafFor
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget AddCommGrpCat) M.isSheaf)
    (Presheaf.imageSieve i.hom.c r)
    ((IsThickening.c_locallySurjective (i := i)).imageSieve_mem r)).amalgamate
      (localActionFamily i M U r m) (localAction_compatible i M hM U r m)

/-- On any open where a chosen local lift exists, the descended action equals the original
action of that lift. -/
theorem act_local (U : Opens X')
    (r : X.presheaf.obj (op ((Opens.map i.hom.base).obj U))) (m : M.val.obj (op U))
    {V : Opens X'} (inclusion : V ⟶ U) (member : Presheaf.imageSieve i.hom.c r inclusion) :
    M.val.map inclusion.op (act i M hM U r m) =
      @SMul.smul (X'.ringCatSheaf.obj.obj (op V)) (M.val.obj (op V)) inferInstance
        (Presheaf.localPreimage i.hom.c r inclusion member) (M.val.map inclusion.op m) := by
  exact Presieve.IsSheafFor.valid_glue _ (localAction_compatible i M hM U r m)
    inclusion member

/-- Applying the projected value of an original scalar recovers its original action. -/
theorem act_projection (U : Opens X') (r : X'.presheaf.obj (op U))
    (m : M.val.obj (op U)) :
    act i M hM U (i.hom.c.app (op U) r) m = r • m := sorry

/-- The descended scalar action commutes with restriction of scalars and module sections. -/
theorem act_restrict {U V : Opens X'} (inclusion : V ⟶ U)
    (r : X.presheaf.obj (op ((Opens.map i.hom.base).obj U))) (m : M.val.obj (op U)) :
    M.val.map inclusion.op (act i M hM U r m) =
      act i M hM V (X.presheaf.map ((Opens.map i.hom.base).map inclusion).op r)
        (M.val.map inclusion.op m) := sorry

/-- The module structure on the original sections with scalars in the reduced structure
sheaf is given by the locally glued action. -/
@[implicit_reducible] def sectionModule (U : Opens X') :
    Module (X.presheaf.obj (op ((Opens.map i.hom.base).obj U))) (M.val.obj (op U)) := by
  have laws :
      (∀ m, act i M hM U 1 m = m) ∧
      (∀ r s m, act i M hM U (r * s) m = act i M hM U r (act i M hM U s m)) ∧
      (∀ r m n, act i M hM U r (m + n) = act i M hM U r m + act i M hM U r n) ∧
      (∀ r, act i M hM U r 0 = 0) ∧
      (∀ r s m, act i M hM U (r + s) m = act i M hM U r m + act i M hM U s m) ∧
      (∀ m, act i M hM U 0 m = 0) := sorry
  exact
    { smul := act i M hM U
      one_smul := laws.1
      mul_smul := laws.2.1
      smul_add := laws.2.2.1
      smul_zero := laws.2.2.2.1
      add_smul := laws.2.2.2.2.1
      zero_smul := laws.2.2.2.2.2 }

private def baseIso : X.carrier ≅ X'.carrier :=
  @asIso _ _ _ _ i.hom.base (IsThickening.base_isIso (i := i))

private def additiveSheaf : TopCat.Sheaf AddCommGrpCat X.carrier :=
  (TopCat.Sheaf.pushforward AddCommGrpCat (baseIso i).inv).obj
    ((SheafOfModules.toSheaf X'.ringCatSheaf).obj M)

@[implicit_reducible] private def transportedSectionModule (U : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((additiveSheaf i M).obj.obj U) :=
  @Module.compHom _ _ _ _ _
    (sectionModule i M hM ((Opens.map (baseIso i).inv).obj U.unop)) _
    (X.ringCatSheaf.obj.map ((Opens.mapMapIso (baseIso i)).counitIso.hom.app U.unop).op).hom

/-- Scalar descent transports the original additive sheaf along the inverse underlying
homeomorphism and equips its sections with the locally glued reduced scalar action. -/
def descend : X.Modules where
  val := @PresheafOfModules.ofPresheaf _ _ X.ringCatSheaf.obj (additiveSheaf i M).obj
    (transportedSectionModule i M hM) (by
      intro U V restriction r m
      change M.val.presheaf.map ((Opens.map (baseIso i).inv).map restriction.unop).op
        (act i M hM _
          (X.presheaf.map ((Opens.mapMapIso (baseIso i)).counitIso.hom.app U.unop).op r) m) =
        act i M hM _
          (X.presheaf.map ((Opens.mapMapIso (baseIso i)).counitIso.hom.app V.unop).op
            (X.presheaf.map restriction r))
          (M.val.presheaf.map ((Opens.map (baseIso i).inv).map restriction.unop).op m)
      erw [act_restrict]
      congr 1
      change X.presheaf.map _ (X.presheaf.map _ r) = X.presheaf.map _ (X.presheaf.map _ r)
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  isSheaf := (additiveSheaf i M).property

/-- The reconstruction map identifies the pushforward of scalar descent with the original
module by the identity reindexing of open sets. -/
def descendPushforwardHom : (i _*).obj (descend i M hM) ⟶ M where
  val := PresheafOfModules.homMk
    { app := fun U => M.val.presheaf.map
        ((Opens.mapMapIso (baseIso i)).unitIso.hom.app U.unop).op
      naturality := by
        intro U V restriction
        ext m
        change M.val.presheaf.map
            ((Opens.mapMapIso (baseIso i)).unitIso.hom.app V.unop).op
            (M.val.presheaf.map
              ((Opens.map (baseIso i).inv).map ((Opens.map i.hom.base).map restriction.unop)).op m) =
          M.val.presheaf.map restriction
            (M.val.presheaf.map ((Opens.mapMapIso (baseIso i)).unitIso.hom.app U.unop).op m)
        erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        rfl }
    (by
      intro U r m
      change M.val.map _ (act i M hM _
        (X.presheaf.map ((Opens.mapMapIso (baseIso i)).counitIso.hom.app
            ((Opens.map i.hom.base).obj U.unop)).op (i.hom.c.app U r)) m) =
        r • M.val.presheaf.map _ m
      have scalar_eq :
          X.presheaf.map ((Opens.mapMapIso (baseIso i)).counitIso.hom.app
              ((Opens.map i.hom.base).obj U.unop)).op (i.hom.c.app U r) =
            i.hom.c.app _ (X'.presheaf.map
              ((Opens.mapMapIso (baseIso i)).unitIso.inv.app U.unop).op r) :=
        (NatTrans.naturality_apply i.hom.c
          ((Opens.mapMapIso (baseIso i)).unitIso.inv.app U.unop).op r).symm
      erw [scalar_eq, act_projection, M.val.map_smul]
      congr 1
      change X'.presheaf.map _ (X'.presheaf.map _ r) = r
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        Iso.hom_inv_id_app, op_id]
      exact X'.presheaf.map_id_apply _ r)

/-- The inverse reconstruction map is the reverse identity reindexing of the same additive
sections, with the descended scalar action. -/
def descendPushforwardInv : M ⟶ (i _*).obj (descend i M hM) where
  val := PresheafOfModules.homMk
    { app := fun U => M.val.presheaf.map
        ((Opens.mapMapIso (baseIso i)).unitIso.inv.app U.unop).op
      naturality := by
        intro U V restriction
        ext m
        change M.val.presheaf.map
            ((Opens.mapMapIso (baseIso i)).unitIso.inv.app V.unop).op
            (M.val.presheaf.map restriction m) =
          M.val.presheaf.map
            ((Opens.map (baseIso i).inv).map ((Opens.map i.hom.base).map restriction.unop)).op
            (M.val.presheaf.map ((Opens.mapMapIso (baseIso i)).unitIso.inv.app U.unop).op m)
        erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
        rfl }
    (by
      intro U r m
      change M.val.map _ (r • m) = act i M hM _
        (X.presheaf.map ((Opens.mapMapIso (baseIso i)).counitIso.hom.app
            ((Opens.map i.hom.base).obj U.unop)).op (i.hom.c.app U r))
        (M.val.presheaf.map _ m)
      have scalar_eq :
          X.presheaf.map ((Opens.mapMapIso (baseIso i)).counitIso.hom.app
              ((Opens.map i.hom.base).obj U.unop)).op (i.hom.c.app U r) =
            i.hom.c.app _ (X'.presheaf.map
              ((Opens.mapMapIso (baseIso i)).unitIso.inv.app U.unop).op r) :=
        (NatTrans.naturality_apply i.hom.c
          ((Opens.mapMapIso (baseIso i)).unitIso.inv.app U.unop).op r).symm
      erw [scalar_eq, act_projection, M.val.map_smul]
      rfl)

set_option maxHeartbeats 800000 in
/-- The two explicit reconstruction maps identify pushforward of the descended module with
the original module. -/
def descendPushforwardIso : (i _*).obj (descend i M hM) ≅ M where
  hom := descendPushforwardHom i M hM
  inv := descendPushforwardInv i M hM
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change M.val.presheaf.map ((Opens.mapMapIso (baseIso i)).unitIso.inv.app U.unop).op
      (M.val.presheaf.map ((Opens.mapMapIso (baseIso i)).unitIso.hom.app U.unop).op m) = m
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id_app, op_id]
    exact M.val.presheaf.map_id_apply _ m
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext m
    change M.val.presheaf.map ((Opens.mapMapIso (baseIso i)).unitIso.hom.app U.unop).op
      (M.val.presheaf.map ((Opens.mapMapIso (baseIso i)).unitIso.inv.app U.unop).op m) = m
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Iso.hom_inv_id_app, op_id]
    exact M.val.presheaf.map_id_apply _ m

/-- A kernel-annihilated module has an explicit inverse to the pullback-pushforward unit,
formed from reconstruction and the adjunction counit. -/
def unitInv : (i _*).obj ((i^*).obj M) ⟶ M :=
  (i _*).map ((i^*).map (descendPushforwardIso i M hM).inv) ≫
    (i _*).map ((pullbackPushforwardAdjunction i).counit.app (descend i M hM)) ≫
      (descendPushforwardIso i M hM).hom

/-- The unit followed by its explicit inverse is the identity on a kernel-annihilated
module. -/
theorem unit_comp_unitInv :
    (pullbackPushforwardAdjunction i).unit.app M ≫ unitInv i M hM = 𝟙 M := sorry

/-- The explicit inverse followed by the unit is the identity on the pullback-pushforward
of a kernel-annihilated module. -/
theorem unitInv_comp_unit :
    unitInv i M hM ≫ (pullbackPushforwardAdjunction i).unit.app M =
      𝟙 ((i _*).obj ((i^*).obj M)) := sorry

end AlgebraicGeometry.RingedSpace.Hom.ScalarDescent
