module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.Module.Component
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Nerve
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

/-!
# Quasi-coherent descent along the nerve of a groupoid scheme

Equivariant quasi-coherent modules correspond to quasi-coherent modules on the
simplicial Zariski site of the nerve.
-/

-- Exposed constructions use private implementation bodies without exporting their names.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Opposite AlgebraicGeometry
open TopCat TopologicalSpace
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The last-vertex map `X_n ⟶ U` of the associated simplicial scheme. -/
private def vertex (n : SimplexCategory) :
    G.simplicialScheme.obj (op n) ⟶ G.U.left :=
  G.simplicialScheme.map (op (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))) ≫ (degreeZero.iso G).hom

/-- In degree `0`, the last-vertex map is `degreeZero.iso.hom`. -/
private theorem vertex_zero : vertex G ⦋0⦌ = (degreeZero.iso G).hom :=
  sorry

/-- The edge map `X_m ⟶ R` associated to a simplex operator `φ`. -/
private def edge {n m : SimplexCategory} (φ : n ⟶ m) :
    G.simplicialScheme.obj (op m) ⟶ G.R.left :=
  G.simplicialScheme.map (op (SimplexCategory.mkOfLe (φ.toOrderHom (Fin.last n.len)) (Fin.last m.len) (Fin.le_last _))) ≫ (degreeOne.iso G).hom

/-- Last-vertex pullback of an equivariant module to degree `n`. -/
private def stageModule (A : G.QCoh) (n : SimplexCategory) :
    Scheme.QCoh (G.simplicialScheme.obj (op n)) :=
  (Scheme.QCoh.pullback (vertex G n)).obj A.obj

/-- The last vertex of `n` maps under `φ` to the target of `edge φ`. -/
private theorem vertex_map_eq_edge_t {n m : SimplexCategory} (φ : n ⟶ m) :
    G.simplicialScheme.map φ.op ≫ vertex G n = edge G φ ≫ G.t.left :=
  sorry

/-- The last vertex of `m` is the source of `edge φ`. -/
private theorem vertex_eq_edge_s {n m : SimplexCategory} (φ : n ⟶ m) :
    vertex G m = edge G φ ≫ G.s.left :=
  sorry

/-- Transition of last-vertex pullbacks along a simplex operator, using the groupoid
action `t^* ⟶ s^*` on the connecting edge. -/
private def stageTransition (A : G.QCoh) {n m : SimplexCategory} (φ : n ⟶ m) :
    (Scheme.QCoh.pullback (G.simplicialScheme.map φ.op)).obj (stageModule G A n) ⟶
      stageModule G A m :=
  (pullbackCompIso (G.simplicialScheme.map φ.op) (vertex G n)).inv.app A.obj ≫
    (pullbackEqIso (vertex_map_eq_edge_t G φ)).hom.app A.obj ≫
      (reindexAction G.t.left G.s.left (edge G φ) A.obj (QCoh.action A)) ≫
        (pullbackEqIso (vertex_eq_edge_s G φ)).inv.app A.obj

/-- Sections of the assembled module over a diagram open, as last-vertex pullback sections. -/
private def toZariskiObj (A : G.QCoh)
    (W : (CategoryTheory.SimplicialObject.zariskiSite (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ) :
    ModuleCat
      ((SimplicialObject.structureSheaf G.simplicialScheme).obj.obj W) :=
  ((stageModule G A W.unop.base.unop).obj).val.obj (op W.unop.opens)

/-- The source open of `η` is contained in the inverse image of the target open. -/
private theorem toZariski_mapsTo_le
    {W Z : (CategoryTheory.SimplicialObject.zariskiSite (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ} (η : W ⟶ Z) :
    Z.unop.opens ≤
      (Opens.map (G.simplicialScheme.map η.unop.base).base).obj W.unop.opens :=
  fun _ hx ↦ η.unop.mapsTo hx

private def toZariskiValSection (A : G.QCoh)
    {W Z : (CategoryTheory.SimplicialObject.zariskiSite (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ} (η : W ⟶ Z) :
    toZariskiObj G A W →
      (ModuleCat.restrictScalars
        ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map η).hom).obj
        (toZariskiObj G A Z) :=
  fun x ↦
    (stageTransition G A η.unop.base.unop).hom.val.app (op Z.unop.opens)
      (eqToHom (congrArg (fun M : (G.simplicialScheme.obj Z.unop.base).Modules ↦
          M.val.obj (op Z.unop.opens))
          (Scheme.QCoh.pullback_obj (G.simplicialScheme.map η.unop.base)
            (stageModule G A W.unop.base.unop)).symm)
        (((Scheme.Modules.pullback (G.simplicialScheme.map η.unop.base)).obj
            (stageModule G A W.unop.base.unop).obj).val.map
          (homOfLE (toZariski_mapsTo_le G η)).op
          (eqToHom (Scheme.Modules.pushforward_obj_obj
              (G.simplicialScheme.map η.unop.base)
              ((Scheme.Modules.pullback (G.simplicialScheme.map η.unop.base)).obj
                (stageModule G A W.unop.base.unop).obj)
              W.unop.opens)
            (((Scheme.Modules.pullbackPushforwardAdjunction
                (G.simplicialScheme.map η.unop.base)).unit.app
                (stageModule G A W.unop.base.unop).obj).val.app (op W.unop.opens) x))))

private theorem toZariskiValMap_linear (A : G.QCoh)
    {W Z : (CategoryTheory.SimplicialObject.zariskiSite
      (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ} (η : W ⟶ Z) :
    (∀ x y, toZariskiValSection G A η (x + y) =
      toZariskiValSection G A η x + toZariskiValSection G A η y) ∧
    (∀ (r : (SimplicialObject.structureSheaf G.simplicialScheme).obj.obj W) x,
      toZariskiValSection G A η (r • x) = r • toZariskiValSection G A η x) := sorry

private def toZariskiValMap (A : G.QCoh)
    {W Z : (CategoryTheory.SimplicialObject.zariskiSite
      (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ} (η : W ⟶ Z) :
    toZariskiObj G A W ⟶
      (ModuleCat.restrictScalars
        ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map η).hom).obj
        (toZariskiObj G A Z) :=
  ModuleCat.ofHom
    (R := (SimplicialObject.structureSheaf G.simplicialScheme).obj.obj W)
    (X := toZariskiObj G A W)
    (Y := (ModuleCat.restrictScalars
      ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map η).hom).obj
      (toZariskiObj G A Z))
    ({ toFun := toZariskiValSection G A η
       map_add' := (toZariskiValMap_linear G A η).1
       map_smul' := (toZariskiValMap_linear G A η).2 } :
      toZariskiObj G A W →ₗ[(SimplicialObject.structureSheaf G.simplicialScheme).obj.obj W]
        (ModuleCat.restrictScalars
          ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map η).hom).obj
          (toZariskiObj G A Z))

private theorem toZariskiPresheaf_laws (A : G.QCoh) :
    (∀ W, toZariskiValMap G A (𝟙 W) =
      (ModuleCat.restrictScalarsId'
        ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map (𝟙 W)).hom
        (congrArg RingCat.Hom.hom
          ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map_id W))).inv.app _) ∧
    (∀ {W Z T} (f : W ⟶ Z) (g : Z ⟶ T),
      toZariskiValMap G A (f ≫ g) = toZariskiValMap G A f ≫
        (ModuleCat.restrictScalars _).map (toZariskiValMap G A g) ≫
          (ModuleCat.restrictScalarsComp'
            ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map f).hom
            ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map g).hom
            ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map (f ≫ g)).hom
            (congrArg RingCat.Hom.hom
              ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map_comp f g))).inv.app _) :=
  sorry

/-- The assembled presheaf of modules on `X_Zar` associated to an equivariant module. -/
private def toZariskiPresheaf (A : G.QCoh) :
    PresheafOfModules.{u}
      (SimplicialObject.structureSheaf G.simplicialScheme).obj where
  obj W := toZariskiObj G A W
  map η := toZariskiValMap G A η
  map_id := (toZariskiPresheaf_laws G A).1
  map_comp := (toZariskiPresheaf_laws G A).2

private theorem toZariskiSheaf_isSheaf (A : G.QCoh) :
    Presheaf.IsSheaf
      (CategoryTheory.SimplicialObject.zariskiTopology
        (SimplicialObject.forgetToTop.obj G.simplicialScheme))
      (toZariskiPresheaf G A).presheaf := sorry

/-- The assembled sheaf of modules on `X_Zar` associated to an equivariant module. -/
private def toZariskiSheaf (A : G.QCoh) :
    SheafOfModules.{u}
      (SimplicialObject.structureSheaf G.simplicialScheme) where
  val := toZariskiPresheaf G A
  isSheaf := toZariskiSheaf_isSheaf G A

private def toZariskiMapApp {A B : G.QCoh} (f : A ⟶ B)
    (W : (CategoryTheory.SimplicialObject.zariskiSite
      (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ) :=
  ((Scheme.QCoh.pullback (vertex G W.unop.base.unop)).map (QCoh.hom f)).hom.val.app
    (op W.unop.opens)

private theorem toZariskiMap_naturality {A B : G.QCoh} (f : A ⟶ B)
    {W Z : (CategoryTheory.SimplicialObject.zariskiSite
      (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ} (η : W ⟶ Z) :
    (toZariskiSheaf G A).val.map η ≫
        (ModuleCat.restrictScalars ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map η).hom).map (toZariskiMapApp G f Z) =
      toZariskiMapApp G f W ≫ (toZariskiSheaf G B).val.map η := sorry

private def toZariskiMap {A B : G.QCoh} (f : A ⟶ B) :
    toZariskiSheaf G A ⟶ toZariskiSheaf G B where
  val := { app := toZariskiMapApp G f
           naturality := toZariskiMap_naturality G f }

private theorem toZariski_isQuasicoherent (A : G.QCoh) :
    (toZariskiSheaf G A).IsQuasicoherent := sorry

private theorem toZariski_laws :
    (∀ A, toZariskiMap G (𝟙 A) = 𝟙 _) ∧
    (∀ {A B C : G.QCoh} (f : A ⟶ B) (g : B ⟶ C),
      toZariskiMap G (f ≫ g) = toZariskiMap G f ≫ toZariskiMap G g) := sorry

/-- The functor sending an equivariant quasi-coherent module on `G` to a quasi-coherent
module on `G.simplicialScheme` Zariski. -/
def toZariski : G.QCoh ⥤ SimplicialObject.QCoh G.simplicialScheme where
  obj A := ⟨toZariskiSheaf G A, toZariski_isQuasicoherent G A⟩
  map f := ObjectProperty.homMk (toZariskiMap G f)
  map_id := fun A ↦ congrArg ObjectProperty.homMk ((toZariski_laws G).1 A)
  map_comp := fun f g ↦ congrArg ObjectProperty.homMk ((toZariski_laws G).2 f g)

/-- Degree-zero restriction of a quasi-coherent module on `X_Zar`, as a quasi-coherent
module on `X_0`. -/
private def degreeZeroModule (F : SimplicialObject.QCoh G.simplicialScheme) :
    Scheme.QCoh (G.simplicialScheme.obj (op ⦋0⦌)) :=
  ⟨(SimplicialObject.moduleComponent G.simplicialScheme (op ⦋0⦌)).obj F.obj, inferInstance⟩

/-- Degree-one restriction of a quasi-coherent module on `X_Zar`, as a quasi-coherent
module on `X_1`. -/
private def degreeOneModule (F : SimplicialObject.QCoh G.simplicialScheme) :
    Scheme.QCoh (G.simplicialScheme.obj (op ⦋1⦌)) :=
  ⟨(SimplicialObject.moduleComponent G.simplicialScheme (op ⦋1⦌)).obj F.obj, inferInstance⟩

/-- The underlying module on `U` obtained by transporting the degree-zero restriction along
`degreeZero.iso`. -/
private def ofZariskiModule (F : SimplicialObject.QCoh G.simplicialScheme) :
    Scheme.QCoh G.U.left :=
  (Scheme.QCoh.pullback (degreeZero.iso G).inv).obj (degreeZeroModule G F)

/-- After identifying `X_0` with `U`, the target map is the face `δ 1`. -/
private theorem target_face :
    G.t.left ≫ (degreeZero.iso G).inv =
      (degreeOne.iso G).inv ≫ G.simplicialScheme.δ (1 : Fin 2) :=
  sorry

/-- After identifying `X_0` with `U`, the source map is the face `δ 0`. -/
private theorem source_face :
    G.s.left ≫ (degreeZero.iso G).inv =
      (degreeOne.iso G).inv ≫ G.simplicialScheme.δ (0 : Fin 2) :=
  sorry

/-- Comparison `δ 1^* F_0 ⟶ F_1` extracted from restriction of the sheaf on `X_Zar`. -/
private def faceOneComparison (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback (G.simplicialScheme.δ (1 : Fin 2))).obj (degreeZeroModule G F) ⟶
      degreeOneModule G F :=
  ObjectProperty.homMk
    (eqToHom (Scheme.QCoh.pullback_obj (G.simplicialScheme.δ (1 : Fin 2))
        (degreeZeroModule G F)) ≫
      SimplicialObject.stageRestrictModules G.simplicialScheme (SimplexCategory.δ (1 : Fin 2)) F)

/-- Comparison `F_1 ⟶ δ 0^* F_0`, the inverse of restriction of the sheaf along `δ 0`. -/
private def faceZeroComparison (F : SimplicialObject.QCoh G.simplicialScheme) :
    degreeOneModule G F ⟶
      (Scheme.QCoh.pullback (G.simplicialScheme.δ (0 : Fin 2))).obj (degreeZeroModule G F) :=
  ObjectProperty.homMk
    ((@asIso _ _ _ _ (SimplicialObject.stageRestrictModules G.simplicialScheme (SimplexCategory.δ (0 : Fin 2)) F)
        (SimplicialObject.stageRestrictModules_isIso G.simplicialScheme (SimplexCategory.δ (0 : Fin 2)) F)).inv ≫
      eqToHom (Scheme.QCoh.pullback_obj (G.simplicialScheme.δ (0 : Fin 2))
        (degreeZeroModule G F)).symm)

/-- Face-descent comparison `δ 1^* F_0 ⟶ δ 0^* F_0` on `X_1`. -/
private def faceComparison (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback (G.simplicialScheme.δ (1 : Fin 2))).obj (degreeZeroModule G F) ⟶
      (Scheme.QCoh.pullback (G.simplicialScheme.δ (0 : Fin 2))).obj (degreeZeroModule G F) :=
  faceOneComparison G F ≫ faceZeroComparison G F

/-- Transport of `faceComparison` along `degreeOne.iso` to a morphism of pullbacks on `R`. -/
private def faceComparisonOnArrows (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback (degreeOne.iso G).inv).obj
        ((Scheme.QCoh.pullback (G.simplicialScheme.δ (1 : Fin 2))).obj
          (degreeZeroModule G F)) ⟶
      (Scheme.QCoh.pullback (degreeOne.iso G).inv).obj
        ((Scheme.QCoh.pullback (G.simplicialScheme.δ (0 : Fin 2))).obj
          (degreeZeroModule G F)) :=
  (Scheme.QCoh.pullback (degreeOne.iso G).inv).map (faceComparison G F)

/-- Compare `t^*` of the transported degree-zero module with the `δ 1` face pullback on `R`. -/
private def ofZariskiActionToFace (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback G.t.left).obj (ofZariskiModule G F) ⟶
      (Scheme.QCoh.pullback (degreeOne.iso G).inv).obj
        ((Scheme.QCoh.pullback (G.simplicialScheme.δ (1 : Fin 2))).obj
          (degreeZeroModule G F)) :=
  (pullbackCompIso G.t.left (degreeZero.iso G).inv).inv.app (degreeZeroModule G F) ≫
    (pullbackEqIso (target_face G)).hom.app (degreeZeroModule G F) ≫
      (pullbackCompIso (degreeOne.iso G).inv (G.simplicialScheme.δ (1 : Fin 2))).hom.app
        (degreeZeroModule G F)

/-- Compare the `δ 0` face pullback on `R` with `s^*` of the transported degree-zero module. -/
private def ofZariskiActionFromFace (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback (degreeOne.iso G).inv).obj
        ((Scheme.QCoh.pullback (G.simplicialScheme.δ (0 : Fin 2))).obj
          (degreeZeroModule G F)) ⟶
      (Scheme.QCoh.pullback G.s.left).obj (ofZariskiModule G F) :=
  (pullbackCompIso (degreeOne.iso G).inv (G.simplicialScheme.δ (0 : Fin 2))).inv.app
      (degreeZeroModule G F) ≫
    (pullbackEqIso (source_face G)).inv.app (degreeZeroModule G F) ≫
      (pullbackCompIso G.s.left (degreeZero.iso G).inv).hom.app (degreeZeroModule G F)

/-- The equivariance map `t^* F ⟶ s^* F` extracted from a quasi-coherent module on `X_Zar`. -/
private def ofZariskiAction (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback G.t.left).obj (ofZariskiModule G F) ⟶
      (Scheme.QCoh.pullback G.s.left).obj (ofZariskiModule G F) :=
  ofZariskiActionToFace G F ≫ faceComparisonOnArrows G F ≫ ofZariskiActionFromFace G F

private theorem ofZariski_cocycle (F : SimplicialObject.QCoh G.simplicialScheme) :
    Cocycle G (ofZariskiModule G F) (ofZariskiAction G F) := sorry

private theorem ofZariski_unit (F : SimplicialObject.QCoh G.simplicialScheme) :
    Unit G (ofZariskiModule G F) (ofZariskiAction G F) := sorry

private def ofZariskiObject (F : SimplicialObject.QCoh G.simplicialScheme) : G.QCoh :=
  QCoh.of (ofZariskiModule G F) (ofZariskiAction G F)
    (ofZariski_cocycle G F) (ofZariski_unit G F)

private def ofZariskiModuleMap {F H : SimplicialObject.QCoh G.simplicialScheme} (φ : F ⟶ H) :
    ofZariskiModule G F ⟶ ofZariskiModule G H :=
  (Scheme.QCoh.pullback (degreeZero.iso G).inv).map
    (ObjectProperty.homMk
      ((SimplicialObject.moduleComponent G.simplicialScheme (op ⦋0⦌)).map φ.hom))

private theorem ofZariskiMap_compatibility
    {F H : SimplicialObject.QCoh G.simplicialScheme} (φ : F ⟶ H) :
    (Scheme.QCoh.pullback G.t.left).map (ofZariskiModuleMap G φ) ≫ ofZariskiAction G H =
      ofZariskiAction G F ≫ (Scheme.QCoh.pullback G.s.left).map (ofZariskiModuleMap G φ) := sorry

private def ofZariskiMap {F H : SimplicialObject.QCoh G.simplicialScheme} (φ : F ⟶ H) :
    ofZariskiObject G F ⟶ ofZariskiObject G H :=
  System.Hom.of (ofZariskiModuleMap G φ) (ofZariskiMap_compatibility G φ)

private theorem ofZariski_laws :
    (∀ F, ofZariskiMap G (𝟙 F) = 𝟙 _) ∧
    (∀ {F H K : SimplicialObject.QCoh G.simplicialScheme} (f : F ⟶ H) (g : H ⟶ K),
      ofZariskiMap G (f ≫ g) = ofZariskiMap G f ≫ ofZariskiMap G g) := sorry

/-- Extract an equivariant module by degree-zero restriction and the two face comparisons. -/
def ofZariski : SimplicialObject.QCoh G.simplicialScheme ⥤ G.QCoh where
  obj F := ofZariskiObject G F
  map φ := ofZariskiMap G φ
  map_id := (ofZariski_laws G).1
  map_comp := (ofZariski_laws G).2

/-- The underlying module of `ofZariski.obj F` is the degree-zero restriction transported along
`degreeZero.iso`. -/
theorem ofZariski_obj (F : SimplicialObject.QCoh G.simplicialScheme) :
    QCoh.obj ((ofZariski G).obj F) = ofZariskiModule G F :=
  rfl

/-- The action of `ofZariski.obj F` is `ofZariskiAction`. -/
theorem ofZariski_action (F : SimplicialObject.QCoh G.simplicialScheme) :
    QCoh.action ((ofZariski G).obj F) = ofZariskiAction G F :=
  rfl

private theorem toZariskiDegreeZeroHom_naturality (A : G.QCoh)
    {W Z : (Opens (G.simplicialScheme.obj (op ⦋0⦌)))ᵒᵖ} (η : W ⟶ Z) :
    (((Scheme.QCoh.pullback (vertex G ⦋0⦌)).obj A.obj).obj).val.map η ≫
        (ModuleCat.restrictScalars (((G.simplicialScheme.obj (op ⦋0⦌)).ringCatSheaf).obj.map η).hom).map ((fun V ↦ 𝟙 ((((Scheme.QCoh.pullback (vertex G ⦋0⦌)).obj A.obj).obj).val.obj V)) Z) =
      (fun V ↦ 𝟙 ((((Scheme.QCoh.pullback (vertex G ⦋0⦌)).obj A.obj).obj).val.obj V)) W ≫ ((degreeZeroModule G ((toZariski G).obj A)).obj).val.map η := sorry

/-- Degree-zero restriction of `toZariski.obj A` identifies on sections with last-vertex
pullback of `A.obj`. -/
private def toZariskiDegreeZeroHom (A : G.QCoh) :
    (Scheme.QCoh.pullback (vertex G ⦋0⦌)).obj A.obj ⟶
      degreeZeroModule G ((toZariski G).obj A) :=
  ObjectProperty.homMk
    { val :=
        { app := fun _ ↦ 𝟙 _
          naturality := toZariskiDegreeZeroHom_naturality G A } }

private theorem toZariskiDegreeZeroInv_naturality (A : G.QCoh)
    {W Z : (Opens (G.simplicialScheme.obj (op ⦋0⦌)))ᵒᵖ} (η : W ⟶ Z) :
    ((degreeZeroModule G ((toZariski G).obj A)).obj).val.map η ≫
        (ModuleCat.restrictScalars (((G.simplicialScheme.obj (op ⦋0⦌)).ringCatSheaf).obj.map η).hom).map ((fun V ↦ 𝟙 (((degreeZeroModule G ((toZariski G).obj A)).obj).val.obj V)) Z) =
      (fun V ↦ 𝟙 (((degreeZeroModule G ((toZariski G).obj A)).obj).val.obj V)) W ≫ (((Scheme.QCoh.pullback (vertex G ⦋0⦌)).obj A.obj).obj).val.map η := sorry

/-- Inverse of `toZariskiDegreeZeroHom` on sections. -/
private def toZariskiDegreeZeroInv (A : G.QCoh) :
    degreeZeroModule G ((toZariski G).obj A) ⟶
      (Scheme.QCoh.pullback (vertex G ⦋0⦌)).obj A.obj :=
  ObjectProperty.homMk
    { val :=
        { app := fun _ ↦ 𝟙 _
          naturality := toZariskiDegreeZeroInv_naturality G A } }

/-- Underlying module map of the unit isomorphism at `A`. -/
private def zariskiQCohUnitHom (A : G.QCoh) :
    A.obj ⟶ ofZariskiModule G ((toZariski G).obj A) :=
  (pullbackIdIso G.U.left).inv.app A.obj ≫
    (pullbackEqIso (Iso.inv_hom_id (degreeZero.iso G))).inv.app A.obj ≫
      (pullbackCompIso (degreeZero.iso G).inv (degreeZero.iso G).hom).hom.app A.obj ≫
        (Functor.whiskerRight (pullbackEqIso (vertex_zero G)).inv
          (Scheme.QCoh.pullback (degreeZero.iso G).inv)).app A.obj ≫
          (Scheme.QCoh.pullback (degreeZero.iso G).inv).map (toZariskiDegreeZeroHom G A)

/-- Underlying module map of the inverse unit isomorphism at `A`. -/
private def zariskiQCohUnitInv (A : G.QCoh) :
    ofZariskiModule G ((toZariski G).obj A) ⟶ A.obj :=
  (Scheme.QCoh.pullback (degreeZero.iso G).inv).map (toZariskiDegreeZeroInv G A) ≫
    (Functor.whiskerRight (pullbackEqIso (vertex_zero G)).hom
      (Scheme.QCoh.pullback (degreeZero.iso G).inv)).app A.obj ≫
      (pullbackCompIso (degreeZero.iso G).inv (degreeZero.iso G).hom).inv.app A.obj ≫
        (pullbackEqIso (Iso.inv_hom_id (degreeZero.iso G))).hom.app A.obj ≫
          (pullbackIdIso G.U.left).hom.app A.obj

private theorem zariskiQCohUnitHom_compatibility (A : G.QCoh) :
    (Scheme.QCoh.pullback G.t.left).map (zariskiQCohUnitHom G A) ≫ QCoh.action ((ofZariski G).obj ((toZariski G).obj A)) =
      QCoh.action (A) ≫ (Scheme.QCoh.pullback G.s.left).map (zariskiQCohUnitHom G A) := sorry

private theorem zariskiQCohUnitInv_compatibility (A : G.QCoh) :
    (Scheme.QCoh.pullback G.t.left).map (zariskiQCohUnitInv G A) ≫ QCoh.action (A) =
      QCoh.action ((ofZariski G).obj ((toZariski G).obj A)) ≫ (Scheme.QCoh.pullback G.s.left).map (zariskiQCohUnitInv G A) := sorry

private theorem zariskiQCohUnitApp_laws (A : G.QCoh) :
    (zariskiQCohUnitHom G A ≫ zariskiQCohUnitInv G A = 𝟙 A.obj) ∧
    (zariskiQCohUnitInv G A ≫ zariskiQCohUnitHom G A =
      𝟙 (ofZariskiModule G ((toZariski G).obj A))) := sorry

/-- The unit isomorphism of the groupoid / Zariski quasi-coherent equivalence, at `A`. -/
private def zariskiQCohUnitApp (A : G.QCoh) :
    A ≅ (ofZariski G).obj ((toZariski G).obj A) where
  hom := System.Hom.of (zariskiQCohUnitHom G A) (zariskiQCohUnitHom_compatibility G A)
  inv := System.Hom.of (zariskiQCohUnitInv G A) (zariskiQCohUnitInv_compatibility G A)
  hom_inv_id := System.Hom.ext (zariskiQCohUnitApp_laws G A).1
  inv_hom_id := System.Hom.ext (zariskiQCohUnitApp_laws G A).2

private theorem zariskiQCohUnitIso_naturality {A B : G.QCoh} (f : A ⟶ B) :
    (𝟭 G.QCoh).map f ≫ (zariskiQCohUnitApp G B).hom =
      (zariskiQCohUnitApp G A).hom ≫ (toZariski G ⋙ ofZariski G).map f := sorry

/-- The unit natural isomorphism `𝟭 ≅ toZariski ⋙ ofZariski`. -/
private def zariskiQCohUnitIso : 𝟭 G.QCoh ≅ toZariski G ⋙ ofZariski G :=
  NatIso.ofComponents (fun A ↦ zariskiQCohUnitApp G A) (fun f ↦ zariskiQCohUnitIso_naturality G f)

/-- Last-vertex followed by `degreeZero.iso.inv` is the last-vertex operator on `X`. -/
private theorem vertex_comp_degreeZero_inv (n : SimplexCategory) :
    vertex G n ≫ (degreeZero.iso G).inv = G.simplicialScheme.map (op (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))) :=
  sorry

/-- Stagewise quasi-coherent module of `F` on `X_n`. -/
private def stageQCoh (F : SimplicialObject.QCoh G.simplicialScheme) (n : SimplexCategory) :
    Scheme.QCoh (G.simplicialScheme.obj (op n)) :=
  ⟨(SimplicialObject.moduleComponent G.simplicialScheme (op n)).obj F.obj, inferInstance⟩

/-- The underlying module of `stageQCoh F n` is the stage restriction of `F`. -/
private theorem stageQCoh_obj (F : SimplicialObject.QCoh G.simplicialScheme) (n : SimplexCategory) :
    (stageQCoh G F n).obj =
      (SimplicialObject.moduleComponent G.simplicialScheme (op n)).obj F.obj :=
  rfl

/-- Last-vertex restriction of `F`, as a morphism of quasi-coherent modules on `X_n`. -/
private def zariskiQCohCounitStage (F : SimplicialObject.QCoh G.simplicialScheme)
    (n : SimplexCategory) :
    (Scheme.QCoh.pullback (vertex G n)).obj (ofZariskiModule G F) ⟶ stageQCoh G F n :=
  (pullbackCompIso (vertex G n) (degreeZero.iso G).inv).inv.app (degreeZeroModule G F) ≫
    (pullbackEqIso (vertex_comp_degreeZero_inv G n)).hom.app (degreeZeroModule G F) ≫
      ObjectProperty.homMk
        (eqToHom (Scheme.QCoh.pullback_obj (G.simplicialScheme.map (op (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))))
            (degreeZeroModule G F)) ≫
          SimplicialObject.stageRestrictModules G.simplicialScheme (SimplexCategory.const ⦋0⦌ n (Fin.last n.len)) F)

/-- The last-vertex comparison of `zariskiQCohCounitStage` is an isomorphism. -/
private theorem zariskiQCohCounitStage_isIso
    (F : SimplicialObject.QCoh G.simplicialScheme) (n : SimplexCategory) :
    IsIso (zariskiQCohCounitStage G F n) :=
  sorry

private def zariskiQCohCounitHomApp (F : SimplicialObject.QCoh G.simplicialScheme)
    (W : (CategoryTheory.SimplicialObject.zariskiSite
      (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ) :
    (((toZariski G).obj ((ofZariski G).obj F)).obj).val.obj W ⟶ (F.obj).val.obj W :=
  (zariskiQCohCounitStage G F W.unop.base.unop).hom.val.app (op W.unop.opens)

private theorem zariskiQCohCounitHom_naturality (F : SimplicialObject.QCoh G.simplicialScheme)
    {W Z : (CategoryTheory.SimplicialObject.zariskiSite
      (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ} (η : W ⟶ Z) :
    (((toZariski G).obj ((ofZariski G).obj F)).obj).val.map η ≫
        (ModuleCat.restrictScalars ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map η).hom).map (zariskiQCohCounitHomApp G F Z) =
      zariskiQCohCounitHomApp G F W ≫ (F.obj).val.map η := sorry

private def zariskiQCohCounitHom (F : SimplicialObject.QCoh G.simplicialScheme) :
    ((toZariski G).obj ((ofZariski G).obj F)).obj ⟶ F.obj where
  val := { app := zariskiQCohCounitHomApp G F
           naturality := zariskiQCohCounitHom_naturality G F }

private def zariskiQCohCounitInvApp (F : SimplicialObject.QCoh G.simplicialScheme)
    (W : (CategoryTheory.SimplicialObject.zariskiSite
      (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ) :
    (F.obj).val.obj W ⟶ (((toZariski G).obj ((ofZariski G).obj F)).obj).val.obj W :=
  (@asIso _ _ _ _ (zariskiQCohCounitStage G F W.unop.base.unop)
      (zariskiQCohCounitStage_isIso G F W.unop.base.unop)).inv.hom.val.app
        (op W.unop.opens)

private theorem zariskiQCohCounitInv_naturality (F : SimplicialObject.QCoh G.simplicialScheme)
    {W Z : (CategoryTheory.SimplicialObject.zariskiSite
      (SimplicialObject.forgetToTop.obj G.simplicialScheme))ᵒᵖ} (η : W ⟶ Z) :
    (F.obj).val.map η ≫
        (ModuleCat.restrictScalars ((SimplicialObject.structureSheaf G.simplicialScheme).obj.map η).hom).map (zariskiQCohCounitInvApp G F Z) =
      zariskiQCohCounitInvApp G F W ≫ (((toZariski G).obj ((ofZariski G).obj F)).obj).val.map η := sorry

private def zariskiQCohCounitInv (F : SimplicialObject.QCoh G.simplicialScheme) :
    F.obj ⟶ ((toZariski G).obj ((ofZariski G).obj F)).obj where
  val := { app := zariskiQCohCounitInvApp G F
           naturality := zariskiQCohCounitInv_naturality G F }

private theorem zariskiQCohCounitApp_laws (F : SimplicialObject.QCoh G.simplicialScheme) :
    (zariskiQCohCounitHom G F ≫ zariskiQCohCounitInv G F = 𝟙 _) ∧
    (zariskiQCohCounitInv G F ≫ zariskiQCohCounitHom G F = 𝟙 _) := sorry

/-- The counit isomorphism of the groupoid / Zariski quasi-coherent equivalence, at `F`. -/
private def zariskiQCohCounitApp (F : SimplicialObject.QCoh G.simplicialScheme) :
    (ofZariski G ⋙ toZariski G).obj F ≅ F where
  hom := ObjectProperty.homMk (zariskiQCohCounitHom G F)
  inv := ObjectProperty.homMk (zariskiQCohCounitInv G F)
  hom_inv_id := congrArg ObjectProperty.homMk (zariskiQCohCounitApp_laws G F).1
  inv_hom_id := congrArg ObjectProperty.homMk (zariskiQCohCounitApp_laws G F).2

private theorem zariskiQCohCounitIso_naturality
    {F H : SimplicialObject.QCoh G.simplicialScheme} (f : F ⟶ H) :
    (ofZariski G ⋙ toZariski G).map f ≫ (zariskiQCohCounitApp G H).hom =
      (zariskiQCohCounitApp G F).hom ≫ (𝟭 (SimplicialObject.QCoh G.simplicialScheme)).map f := sorry

/-- The counit natural isomorphism `ofZariski ⋙ toZariski ≅ 𝟭`. -/
private def zariskiQCohCounitIso :
    ofZariski G ⋙ toZariski G ≅ 𝟭 (SimplicialObject.QCoh G.simplicialScheme) :=
  NatIso.ofComponents (fun F ↦ zariskiQCohCounitApp G F) (fun f ↦ zariskiQCohCounitIso_naturality G f)

/-- The category of quasi-coherent modules on a groupoid scheme is equivalent to the
category of quasi-coherent modules on the Zariski site of the associated simplicial scheme. -/
def quasiCoherentZariskiEquivalence : G.QCoh ≌ SimplicialObject.QCoh G.simplicialScheme :=
  CategoryTheory.Equivalence.mk (toZariski G) (ofZariski G)
    (zariskiQCohUnitIso G) (zariskiQCohCounitIso G)

/-- The forward functor of `quasiCoherentZariskiEquivalence` is `toZariski`. -/
theorem quasiCoherentZariskiEquivalence_functor :
    (quasiCoherentZariskiEquivalence G).functor = toZariski G :=
  rfl

/-- The inverse functor of `quasiCoherentZariskiEquivalence` is `ofZariski`. -/
theorem quasiCoherentZariskiEquivalence_inverse :
    (quasiCoherentZariskiEquivalence G).inverse = ofZariski G :=
  rfl

end AlgebraicGeometry.GroupoidScheme
