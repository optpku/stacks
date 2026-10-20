module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.BaseChange.Sections

@[expose] public section
open CategoryTheory TopologicalSpace Topology Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
noncomputable section
universe u

namespace AlgebraicGeometry.RingedSpace.OpenSubspace.BaseChange

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier)

/-- Structure-ring compatibility on the same image open. This is fixed-map
coherence of the actual restricted ringed-space morphism, not an input premise. -/
theorem sectionScalar_forward (W : Opens (Y.restrict V.isOpenEmbedding).carrier) :
    f.hom.c.app (op (V.isOpenEmbedding.functor.obj W)) ≫
      X.presheaf.map (eqToHom (sectionOpen_eq f V W).symm).op =
        (restrictedMorphismToOpen f V).hom.c.app (op W) := sorry

/-- The two explicitly defined additive section maps are inverse. -/
theorem sectionInv_hom (M : X.Modules) (W : Opens (Y.restrict V.isOpenEmbedding).carrier)
    (m : ((literalSource f V).obj M).val.obj (op W)) :
    sectionInv f V M W (sectionHom f V M W m) = m := by
  change (M.val.presheaf.map (eqToHom (sectionOpen_eq f V W).symm).op ≫
    M.val.presheaf.map (eqToHom (sectionOpen_eq f V W)).op) m = m
  rw [← Functor.map_comp]
  have h : (eqToHom (sectionOpen_eq f V W).symm).op ≫
      (eqToHom (sectionOpen_eq f V W)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [h]
  exact ConcreteCategory.congr_hom (M.val.presheaf.map_id _) m

/-- The reverse composite is also the identity on actual sections. -/
theorem sectionHom_inv (M : X.Modules) (W : Opens (Y.restrict V.isOpenEmbedding).carrier)
    (m : ((literalTarget f V).obj M).val.obj (op W)) :
    sectionHom f V M W (sectionInv f V M W m) = m := by
  change (M.val.presheaf.map (eqToHom (sectionOpen_eq f V W)).op ≫
    M.val.presheaf.map (eqToHom (sectionOpen_eq f V W).symm).op) m = m
  rw [← Functor.map_comp]
  have h : (eqToHom (sectionOpen_eq f V W)).op ≫
      (eqToHom (sectionOpen_eq f V W).symm).op = 𝟙 _ := Subsingleton.elim _ _
  rw [h]
  exact ConcreteCategory.congr_hom (M.val.presheaf.map_id _) m

/-- Linearity over the intrinsic restricted ring follows from the fixed ring map. -/
theorem sectionHom_smul (M : X.Modules) (W : Opens (Y.restrict V.isOpenEmbedding).carrier)
    (r : (RingedSpace.ringCatSheaf (Y.restrict V.isOpenEmbedding)).obj.obj (op W))
    (m : ((literalSource f V).obj M).val.obj (op W)) :
    sectionHom f V M W (r • m) = r • sectionHom f V M W m := by
  have hmap := M.val.map_smul (eqToHom (sectionOpen_eq f V W).symm).op
    ((RingedSpace.Hom.toRingCatSheafHom f).hom.app
      (op (V.isOpenEmbedding.functor.obj W)) r) m
  have hr := ConcreteCategory.congr_hom (sectionScalar_forward f V W) r
  let B := op ((preimageOpen f V).isOpenEmbedding.functor.obj
    ((Opens.map (restrictedMorphismToOpen f V).hom.base).obj W))
  let act : X.ringCatSheaf.obj.obj B → M.val.obj B → M.val.obj B :=
    fun r m => @SMul.smul _ _ (M.val.obj B).isModule.toSMul r m
  exact hmap.trans (congrArg (fun s => act s (sectionHom f V M W m)) hr)

/-- Inverse linearity is proved using the concrete inverse laws and forward linearity. -/
theorem sectionInv_smul (M : X.Modules) (W : Opens (Y.restrict V.isOpenEmbedding).carrier)
    (r : (RingedSpace.ringCatSheaf (Y.restrict V.isOpenEmbedding)).obj.obj (op W))
    (m : ((literalTarget f V).obj M).val.obj (op W)) :
    sectionInv f V M W (r • m) = r • sectionInv f V M W m := by
  apply Function.LeftInverse.injective (sectionInv_hom f V M W)
  rw [sectionHom_inv, sectionHom_smul, sectionHom_inv]

/-- The forward linear section map has the exact underlying restriction function. -/
def sectionHomLinear (M : X.Modules) (W : Opens (Y.restrict V.isOpenEmbedding).carrier) :
    ((literalSource f V).obj M).val.obj (op W) ⟶
      ((literalTarget f V).obj M).val.obj (op W) :=
  ModuleCat.ofHom
    (X := ((literalSource f V).obj M).val.obj (op W))
    (Y := ((literalTarget f V).obj M).val.obj (op W))
    { toFun := sectionHom f V M W
      map_add' := (sectionHom f V M W).map_add
      map_smul' := sectionHom_smul f V M W }

/-- The inverse linear section map contains the actual reverse restriction data. -/
def sectionInvLinear (M : X.Modules) (W : Opens (Y.restrict V.isOpenEmbedding).carrier) :
    ((literalTarget f V).obj M).val.obj (op W) ⟶
      ((literalSource f V).obj M).val.obj (op W) :=
  ModuleCat.ofHom
    (X := ((literalTarget f V).obj M).val.obj (op W))
    (Y := ((literalSource f V).obj M).val.obj (op W))
    { toFun := sectionInv f V M W
      map_add' := (sectionInv f V M W).map_add
      map_smul' := sectionInv_smul f V M W }

end AlgebraicGeometry.RingedSpace.OpenSubspace.BaseChange
