/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent
public import stacks_project.Chap85.Lemma_85_29_1_Nerve
public import stacks_project.Chap85.Lemma_85_29_2_Quasicoherent

/-!
# Equivalence between groupoid quasi-coherent modules and modules on `X_Zar`

A groupoid scheme `G` over `S` has associated simplicial scheme `G.simplicialScheme`. The
category `G.QCoh` of equivariant quasi-coherent modules is equivalent to the category of
quasi-coherent modules on the Zariski ringed site of that simplicial scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Opposite AlgebraicGeometry
open TopCat TopologicalSpace
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The last-vertex operator `τ^n_n : ⦋0⦌ ⟶ n`, sending `0` to `Fin.last n.len`. -/
def vertexOp (n : SimplexCategory) : ⦋0⦌ ⟶ n :=
  SimplexCategory.const ⦋0⦌ n (Fin.last n.len)

/-- `vertexOp n` is `SimplexCategory.const ⦋0⦌ n (Fin.last n.len)`. -/
theorem vertexOp_eq (n : SimplexCategory) :
    vertexOp n = SimplexCategory.const ⦋0⦌ n (Fin.last n.len) :=
  sorry

/-- The last-vertex map `X_n ⟶ U` of the associated simplicial scheme. -/
def vertex (n : SimplexCategory) :
    G.simplicialScheme.obj (op n) ⟶ G.U.left :=
  G.simplicialScheme.map (op (vertexOp n)) ≫ (degreeZero.iso G).hom

/-- `vertex n` is last-vertex pullback of `degreeZero.iso`. -/
theorem vertex_eq (n : SimplexCategory) :
    vertex G n =
      G.simplicialScheme.map (op (vertexOp n)) ≫ (degreeZero.iso G).hom :=
  sorry

/-- In degree `0`, the last-vertex map is `degreeZero.iso.hom`. -/
theorem vertex_zero : vertex G ⦋0⦌ = (degreeZero.iso G).hom :=
  sorry

/-- The edge operator `τ^m_{φ(n)m} : ⦋1⦌ ⟶ m` from `φ (last n)` to `last m`. -/
def edgeOp {n m : SimplexCategory} (φ : n ⟶ m) : ⦋1⦌ ⟶ m :=
  SimplexCategory.mkOfLe (φ.toOrderHom (Fin.last n.len)) (Fin.last m.len) (Fin.le_last _)

/-- The edge map `X_m ⟶ R` associated to a simplex operator `φ`. -/
def edge {n m : SimplexCategory} (φ : n ⟶ m) :
    G.simplicialScheme.obj (op m) ⟶ G.R.left :=
  G.simplicialScheme.map (op (edgeOp φ)) ≫ (degreeOne.iso G).hom

/-- `edge φ` is the degree-one identification of `X.map (op (edgeOp φ))`. -/
theorem edge_eq {n m : SimplexCategory} (φ : n ⟶ m) :
    edge G φ = G.simplicialScheme.map (op (edgeOp φ)) ≫ (degreeOne.iso G).hom :=
  sorry

/-- Last-vertex pullback of an equivariant module to degree `n`. -/
def stageModule (A : G.QCoh) (n : SimplexCategory) :
    Scheme.QCoh (G.simplicialScheme.obj (op n)) :=
  (Scheme.QCoh.pullback (vertex G n)).obj A.obj

/-- `stageModule A n` is pullback of `A.obj` along `vertex n`. -/
theorem stageModule_eq (A : G.QCoh) (n : SimplexCategory) :
    stageModule G A n = (Scheme.QCoh.pullback (vertex G n)).obj A.obj :=
  sorry

/-- The last vertex of `n` maps under `φ` to the target of `edge φ`. -/
theorem vertex_map_eq_edge_t {n m : SimplexCategory} (φ : n ⟶ m) :
    G.simplicialScheme.map φ.op ≫ vertex G n = edge G φ ≫ G.t.left :=
  sorry

/-- The last vertex of `m` is the source of `edge φ`. -/
theorem vertex_eq_edge_s {n m : SimplexCategory} (φ : n ⟶ m) :
    vertex G m = edge G φ ≫ G.s.left :=
  sorry

/-- Transition of last-vertex pullbacks along a simplex operator, using the groupoid
action `t^* ⟶ s^*` on the connecting edge. -/
def stageTransition (A : G.QCoh) {n m : SimplexCategory} (φ : n ⟶ m) :
    (Scheme.QCoh.pullback (G.simplicialScheme.map φ.op)).obj (stageModule G A n) ⟶
      stageModule G A m :=
  (pullbackCompIso (G.simplicialScheme.map φ.op) (vertex G n)).inv.app A.obj ≫
    (pullbackEqIso (vertex_map_eq_edge_t G φ)).hom.app A.obj ≫
      (reindexAction G.t.left G.s.left (edge G φ) A.obj (QCoh.action A)) ≫
        (pullbackEqIso (vertex_eq_edge_s G φ)).inv.app A.obj

/-- Package an additive map of underlying sections as a morphism in `ModuleCat`. -/
def moduleCatHomOfFun {R : RingCat.{u}} {M N : ModuleCat.{u} R} (f : M → N) : M ⟶ N :=
  ModuleCat.ofHom
    { toFun := f
      map_add' := sorry
      map_smul' := sorry }

/-- Sections of the assembled module over a diagram open, as last-vertex pullback sections. -/
def toZariskiObj (A : G.QCoh)
    (W : ((SimplicialObject.zariskiRingedSite G.simplicialScheme).carrier)ᵒᵖ) :
    ModuleCat
      ((SimplicialObject.zariskiRingedSite G.simplicialScheme).structureSheaf.obj.obj W) :=
  ((stageModule G A W.unop.base.unop).obj).val.obj (op W.unop.opens)

/-- The source open of `η` is contained in the inverse image of the target open. -/
theorem toZariski_mapsTo_le (A : G.QCoh)
    {W Z : ((SimplicialObject.zariskiRingedSite G.simplicialScheme).carrier)ᵒᵖ} (η : W ⟶ Z) :
    Z.unop.opens ≤
      (Opens.map (G.simplicialScheme.map η.unop.base).base).obj W.unop.opens :=
  sorry

/-- Restriction of the assembled module along a morphism of diagram opens. -/
def toZariskiValMap (A : G.QCoh)
    {W Z : ((SimplicialObject.zariskiRingedSite G.simplicialScheme).carrier)ᵒᵖ} (η : W ⟶ Z) :
    toZariskiObj G A W ⟶
      (ModuleCat.restrictScalars
        ((SimplicialObject.zariskiRingedSite G.simplicialScheme).structureSheaf.obj.map η).hom).obj
        (toZariskiObj G A Z) :=
  moduleCatHomOfFun (fun x ↦
    (stageTransition G A η.unop.base.unop).hom.val.app (op Z.unop.opens)
      (eqToHom (congrArg (fun M : (G.simplicialScheme.obj Z.unop.base).Modules ↦
          M.val.obj (op Z.unop.opens))
          (Scheme.QCoh.pullback_obj (G.simplicialScheme.map η.unop.base)
            (stageModule G A W.unop.base.unop)).symm)
        (((Scheme.Modules.pullback (G.simplicialScheme.map η.unop.base)).obj
            (stageModule G A W.unop.base.unop).obj).val.map
          (homOfLE (toZariski_mapsTo_le G A η)).op
          (eqToHom (Scheme.Modules.pushforward_obj_obj
              (G.simplicialScheme.map η.unop.base)
              ((Scheme.Modules.pullback (G.simplicialScheme.map η.unop.base)).obj
                (stageModule G A W.unop.base.unop).obj)
              W.unop.opens)
            (((Scheme.Modules.pullbackPushforwardAdjunction
                (G.simplicialScheme.map η.unop.base)).unit.app
                (stageModule G A W.unop.base.unop).obj).val.app (op W.unop.opens) x)))))

/-- The assembled presheaf of modules on `X_Zar` associated to an equivariant module. -/
def toZariskiPresheaf (A : G.QCoh) :
    PresheafOfModules.{u}
      (SimplicialObject.zariskiRingedSite G.simplicialScheme).structureSheaf.obj where
  obj W := toZariskiObj G A W
  map η := toZariskiValMap G A η
  map_id := sorry
  map_comp := sorry

/-- The assembled sheaf of modules on `X_Zar` associated to an equivariant module. -/
def toZariskiSheaf (A : G.QCoh) :
    SheafOfModules.{u}
      (SimplicialObject.zariskiRingedSite G.simplicialScheme).structureSheaf where
  val := toZariskiPresheaf G A
  isSheaf := sorry

/-- The morphism of assembled sheaves induced by an equivariant module morphism. -/
def toZariskiMap {A B : G.QCoh} (f : A ⟶ B) :
    toZariskiSheaf G A ⟶ toZariskiSheaf G B where
  val :=
    { app := fun W ↦
        ((Scheme.QCoh.pullback (vertex G W.unop.base.unop)).map (QCoh.hom f)).hom.val.app
          (op W.unop.opens)
      naturality := sorry }

/-- The functor sending an equivariant quasi-coherent module on `G` to a quasi-coherent
module on `G.simplicialScheme` Zariski. -/
def toZariski : G.QCoh ⥤ SimplicialObject.QCoh G.simplicialScheme where
  obj A := ⟨toZariskiSheaf G A, sorry⟩
  map f := ObjectProperty.homMk (toZariskiMap G f)
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- Degree-zero restriction of a quasi-coherent module on `X_Zar`, as a quasi-coherent
module on `X_0`. -/
def degreeZeroModule (F : SimplicialObject.QCoh G.simplicialScheme) :
    Scheme.QCoh (G.simplicialScheme.obj (op ⦋0⦌)) :=
  ⟨(SimplicialObject.moduleComponent G.simplicialScheme (op ⦋0⦌)).obj F.obj, inferInstance⟩

/-- Degree-one restriction of a quasi-coherent module on `X_Zar`, as a quasi-coherent
module on `X_1`. -/
def degreeOneModule (F : SimplicialObject.QCoh G.simplicialScheme) :
    Scheme.QCoh (G.simplicialScheme.obj (op ⦋1⦌)) :=
  ⟨(SimplicialObject.moduleComponent G.simplicialScheme (op ⦋1⦌)).obj F.obj, inferInstance⟩

/-- The underlying module on `U` obtained by transporting the degree-zero restriction along
`degreeZero.iso`. -/
def ofZariskiModule (F : SimplicialObject.QCoh G.simplicialScheme) :
    Scheme.QCoh G.U.left :=
  (Scheme.QCoh.pullback (degreeZero.iso G).inv).obj (degreeZeroModule G F)

/-- After identifying `X_0` with `U`, the target map is the face `δ 1`. -/
theorem target_face :
    G.t.left ≫ (degreeZero.iso G).inv =
      (degreeOne.iso G).inv ≫ G.simplicialScheme.δ (1 : Fin 2) :=
  sorry

/-- After identifying `X_0` with `U`, the source map is the face `δ 0`. -/
theorem source_face :
    G.s.left ≫ (degreeZero.iso G).inv =
      (degreeOne.iso G).inv ≫ G.simplicialScheme.δ (0 : Fin 2) :=
  sorry

/-- Diagram-open morphism for a simplex operator `φ : n ⟶ m` on an open of `X_n`. -/
def simplexDiagramHom {n m : SimplexCategory} (φ : n ⟶ m)
    (V : Opens ((SimplicialObject.forgetToTop.obj G.simplicialScheme).obj (op n))) :
    DiagramOpens.ofOpens (SimplicialObject.forgetToTop.obj G.simplicialScheme) (op m)
        ((Opens.map ((SimplicialObject.forgetToTop.obj G.simplicialScheme).map φ.op)).obj V) ⟶
      DiagramOpens.ofOpens (SimplicialObject.forgetToTop.obj G.simplicialScheme) (op n) V :=
  DiagramOpens.homMk φ.op sorry

/-- The stage map of `simplexDiagramHom φ V` is `φ.op`. -/
theorem simplexDiagramHom_base {n m : SimplexCategory} (φ : n ⟶ m)
    (V : Opens ((SimplicialObject.forgetToTop.obj G.simplicialScheme).obj (op n))) :
    (simplexDiagramHom G φ V).base = φ.op :=
  sorry

/-- Direct-image comparison `F_n ⟶ (X(φ))_* F_m` whose components are restriction of `F`
along `simplexDiagramHom φ`. -/
def stageDirect {n m : SimplexCategory} (φ : n ⟶ m)
    (F : SimplicialObject.QCoh G.simplicialScheme) :
    (SimplicialObject.moduleComponent G.simplicialScheme (op n)).obj F.obj ⟶
      (Scheme.Modules.pushforward (G.simplicialScheme.map φ.op)).obj
        ((SimplicialObject.moduleComponent G.simplicialScheme (op m)).obj F.obj) where
  val :=
    { app := fun V ↦
        moduleCatHomOfFun (fun x ↦ F.obj.val.map (simplexDiagramHom G φ V.unop).op x)
      naturality := sorry }

/-- The source comparison `X(φ)^* F_n ⟶ F_m` is the adjunction mate of `stageDirect`. -/
def stageRestrictModules {n m : SimplexCategory} (φ : n ⟶ m)
    (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.Modules.pullback (G.simplicialScheme.map φ.op)).obj
      ((SimplicialObject.moduleComponent G.simplicialScheme (op n)).obj F.obj) ⟶
      (SimplicialObject.moduleComponent G.simplicialScheme (op m)).obj F.obj :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (G.simplicialScheme.map φ.op)).homEquiv
      ((SimplicialObject.moduleComponent G.simplicialScheme (op n)).obj F.obj)
      ((SimplicialObject.moduleComponent G.simplicialScheme (op m)).obj F.obj)).symm
    (stageDirect G φ F)

/-- The adjunction mate of `stageRestrictModules` is `stageDirect`. -/
theorem stageRestrictModules_homEquiv {n m : SimplexCategory} (φ : n ⟶ m)
    (F : SimplicialObject.QCoh G.simplicialScheme) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (G.simplicialScheme.map φ.op)).homEquiv
        ((SimplicialObject.moduleComponent G.simplicialScheme (op n)).obj F.obj)
        ((SimplicialObject.moduleComponent G.simplicialScheme (op m)).obj F.obj))
      (stageRestrictModules G φ F) =
    stageDirect G φ F :=
  sorry

/-- Restriction along a simplex operator is an isomorphism for quasi-coherent modules on
`X_Zar`. -/
instance stageRestrictModules_isIso {n m : SimplexCategory} (φ : n ⟶ m)
    (F : SimplicialObject.QCoh G.simplicialScheme) :
    IsIso (stageRestrictModules G φ F) :=
  sorry

/-- Comparison `δ 1^* F_0 ⟶ F_1` extracted from restriction of the sheaf on `X_Zar`. -/
def faceOneComparison (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback (G.simplicialScheme.δ (1 : Fin 2))).obj (degreeZeroModule G F) ⟶
      degreeOneModule G F :=
  ObjectProperty.homMk
    (eqToHom (Scheme.QCoh.pullback_obj (G.simplicialScheme.δ (1 : Fin 2))
        (degreeZeroModule G F)) ≫
      stageRestrictModules G (SimplexCategory.δ (1 : Fin 2)) F)

/-- Comparison `F_1 ⟶ δ 0^* F_0`, the inverse of restriction of the sheaf along `δ 0`. -/
def faceZeroComparison (F : SimplicialObject.QCoh G.simplicialScheme) :
    degreeOneModule G F ⟶
      (Scheme.QCoh.pullback (G.simplicialScheme.δ (0 : Fin 2))).obj (degreeZeroModule G F) :=
  ObjectProperty.homMk
    ((@asIso _ _ _ _ (stageRestrictModules G (SimplexCategory.δ (0 : Fin 2)) F)
        (stageRestrictModules_isIso G (SimplexCategory.δ (0 : Fin 2)) F)).inv ≫
      eqToHom (Scheme.QCoh.pullback_obj (G.simplicialScheme.δ (0 : Fin 2))
        (degreeZeroModule G F)).symm)

/-- Face-descent comparison `δ 1^* F_0 ⟶ δ 0^* F_0` on `X_1`. -/
def faceComparison (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback (G.simplicialScheme.δ (1 : Fin 2))).obj (degreeZeroModule G F) ⟶
      (Scheme.QCoh.pullback (G.simplicialScheme.δ (0 : Fin 2))).obj (degreeZeroModule G F) :=
  faceOneComparison G F ≫ faceZeroComparison G F

/-- Transport of `faceComparison` along `degreeOne.iso` to a morphism of pullbacks on `R`. -/
def faceComparisonOnArrows (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback (degreeOne.iso G).inv).obj
        ((Scheme.QCoh.pullback (G.simplicialScheme.δ (1 : Fin 2))).obj
          (degreeZeroModule G F)) ⟶
      (Scheme.QCoh.pullback (degreeOne.iso G).inv).obj
        ((Scheme.QCoh.pullback (G.simplicialScheme.δ (0 : Fin 2))).obj
          (degreeZeroModule G F)) :=
  (Scheme.QCoh.pullback (degreeOne.iso G).inv).map (faceComparison G F)

/-- Compare `t^*` of the transported degree-zero module with the `δ 1` face pullback on `R`. -/
def ofZariskiActionToFace (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback G.t.left).obj (ofZariskiModule G F) ⟶
      (Scheme.QCoh.pullback (degreeOne.iso G).inv).obj
        ((Scheme.QCoh.pullback (G.simplicialScheme.δ (1 : Fin 2))).obj
          (degreeZeroModule G F)) :=
  (pullbackCompIso G.t.left (degreeZero.iso G).inv).inv.app (degreeZeroModule G F) ≫
    (pullbackEqIso (target_face G)).hom.app (degreeZeroModule G F) ≫
      (pullbackCompIso (degreeOne.iso G).inv (G.simplicialScheme.δ (1 : Fin 2))).hom.app
        (degreeZeroModule G F)

/-- Compare the `δ 0` face pullback on `R` with `s^*` of the transported degree-zero module. -/
def ofZariskiActionFromFace (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback (degreeOne.iso G).inv).obj
        ((Scheme.QCoh.pullback (G.simplicialScheme.δ (0 : Fin 2))).obj
          (degreeZeroModule G F)) ⟶
      (Scheme.QCoh.pullback G.s.left).obj (ofZariskiModule G F) :=
  (pullbackCompIso (degreeOne.iso G).inv (G.simplicialScheme.δ (0 : Fin 2))).inv.app
      (degreeZeroModule G F) ≫
    (pullbackEqIso (source_face G)).inv.app (degreeZeroModule G F) ≫
      (pullbackCompIso G.s.left (degreeZero.iso G).inv).hom.app (degreeZeroModule G F)

/-- The equivariance map `t^* F ⟶ s^* F` extracted from a quasi-coherent module on `X_Zar`. -/
def ofZariskiAction (F : SimplicialObject.QCoh G.simplicialScheme) :
    (Scheme.QCoh.pullback G.t.left).obj (ofZariskiModule G F) ⟶
      (Scheme.QCoh.pullback G.s.left).obj (ofZariskiModule G F) :=
  ofZariskiActionToFace G F ≫ faceComparisonOnArrows G F ≫ ofZariskiActionFromFace G F

/-- The inverse functor, extracting an equivariant module from a quasi-coherent module on
`X_Zar`. -/
def ofZariski : SimplicialObject.QCoh G.simplicialScheme ⥤ G.QCoh where
  obj F :=
    QCoh.of (ofZariskiModule G F) (ofZariskiAction G F) sorry sorry
  map {F H} φ :=
    System.Hom.of
      ((Scheme.QCoh.pullback (degreeZero.iso G).inv).map
        (ObjectProperty.homMk
          ((SimplicialObject.moduleComponent G.simplicialScheme (op ⦋0⦌)).map φ.hom)))
      sorry
  map_id := fun _ ↦ sorry
  map_comp := fun _ _ ↦ sorry

/-- The underlying module of `ofZariski.obj F` is the degree-zero restriction transported along
`degreeZero.iso`. -/
theorem ofZariski_obj (F : SimplicialObject.QCoh G.simplicialScheme) :
    QCoh.obj ((ofZariski G).obj F) = ofZariskiModule G F :=
  sorry

/-- The action of `ofZariski.obj F` is `ofZariskiAction`. -/
theorem ofZariski_action (F : SimplicialObject.QCoh G.simplicialScheme) :
    QCoh.action ((ofZariski G).obj F) = ofZariskiAction G F :=
  sorry

/-- After `degreeZero.iso`, the degree-zero restriction of `toZariski.obj A` recovers `A.obj`. -/
theorem toZariski_obj_component0 (A : G.QCoh) :
    ofZariskiModule G ((toZariski G).obj A) =
      (Scheme.QCoh.pullback (degreeZero.iso G).inv).obj
        ((Scheme.QCoh.pullback (vertex G ⦋0⦌)).obj A.obj) :=
  sorry

/-- Degree-zero restriction of `toZariski.obj A` identifies on sections with last-vertex
pullback of `A.obj`. -/
def toZariskiDegreeZeroHom (A : G.QCoh) :
    (Scheme.QCoh.pullback (vertex G ⦋0⦌)).obj A.obj ⟶
      degreeZeroModule G ((toZariski G).obj A) :=
  ObjectProperty.homMk
    { val :=
        { app := fun V ↦ moduleCatHomOfFun (fun x ↦ x)
          naturality := sorry } }

/-- Inverse of `toZariskiDegreeZeroHom` on sections. -/
def toZariskiDegreeZeroInv (A : G.QCoh) :
    degreeZeroModule G ((toZariski G).obj A) ⟶
      (Scheme.QCoh.pullback (vertex G ⦋0⦌)).obj A.obj :=
  ObjectProperty.homMk
    { val :=
        { app := fun V ↦ moduleCatHomOfFun (fun x ↦ x)
          naturality := sorry } }

/-- Underlying module map of the unit isomorphism at `A`. -/
def zariskiQCohUnitHom (A : G.QCoh) :
    A.obj ⟶ ofZariskiModule G ((toZariski G).obj A) :=
  (pullbackIdIso G.U.left).inv.app A.obj ≫
    (pullbackEqIso (Iso.inv_hom_id (degreeZero.iso G))).inv.app A.obj ≫
      (pullbackCompIso (degreeZero.iso G).inv (degreeZero.iso G).hom).hom.app A.obj ≫
        (Functor.whiskerRight (pullbackEqIso (vertex_zero G)).inv
          (Scheme.QCoh.pullback (degreeZero.iso G).inv)).app A.obj ≫
          (Scheme.QCoh.pullback (degreeZero.iso G).inv).map (toZariskiDegreeZeroHom G A)

/-- Underlying module map of the inverse unit isomorphism at `A`. -/
def zariskiQCohUnitInv (A : G.QCoh) :
    ofZariskiModule G ((toZariski G).obj A) ⟶ A.obj :=
  (Scheme.QCoh.pullback (degreeZero.iso G).inv).map (toZariskiDegreeZeroInv G A) ≫
    (Functor.whiskerRight (pullbackEqIso (vertex_zero G)).hom
      (Scheme.QCoh.pullback (degreeZero.iso G).inv)).app A.obj ≫
      (pullbackCompIso (degreeZero.iso G).inv (degreeZero.iso G).hom).inv.app A.obj ≫
        (pullbackEqIso (Iso.inv_hom_id (degreeZero.iso G))).hom.app A.obj ≫
          (pullbackIdIso G.U.left).hom.app A.obj

/-- The unit isomorphism of the groupoid / Zariski quasi-coherent equivalence, at `A`. -/
def zariskiQCohUnitApp (A : G.QCoh) :
    A ≅ (ofZariski G).obj ((toZariski G).obj A) where
  hom := System.Hom.of (zariskiQCohUnitHom G A) sorry
  inv := System.Hom.of (zariskiQCohUnitInv G A) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The unit natural isomorphism `𝟭 ≅ toZariski ⋙ ofZariski`. -/
def zariskiQCohUnitIso : 𝟭 G.QCoh ≅ toZariski G ⋙ ofZariski G :=
  NatIso.ofComponents (fun A ↦ zariskiQCohUnitApp G A) sorry

/-- Last-vertex followed by `degreeZero.iso.inv` is the last-vertex operator on `X`. -/
theorem vertex_comp_degreeZero_inv (n : SimplexCategory) :
    vertex G n ≫ (degreeZero.iso G).inv = G.simplicialScheme.map (op (vertexOp n)) :=
  sorry

/-- Stagewise quasi-coherent module of `F` on `X_n`. -/
def stageQCoh (F : SimplicialObject.QCoh G.simplicialScheme) (n : SimplexCategory) :
    Scheme.QCoh (G.simplicialScheme.obj (op n)) :=
  ⟨(SimplicialObject.moduleComponent G.simplicialScheme (op n)).obj F.obj, inferInstance⟩

/-- The underlying module of `stageQCoh F n` is the stage restriction of `F`. -/
theorem stageQCoh_obj (F : SimplicialObject.QCoh G.simplicialScheme) (n : SimplexCategory) :
    (stageQCoh G F n).obj =
      (SimplicialObject.moduleComponent G.simplicialScheme (op n)).obj F.obj :=
  sorry

/-- Last-vertex restriction of `F`, as a morphism of quasi-coherent modules on `X_n`. -/
def zariskiQCohCounitStage (F : SimplicialObject.QCoh G.simplicialScheme)
    (n : SimplexCategory) :
    (Scheme.QCoh.pullback (vertex G n)).obj (ofZariskiModule G F) ⟶ stageQCoh G F n :=
  (pullbackCompIso (vertex G n) (degreeZero.iso G).inv).inv.app (degreeZeroModule G F) ≫
    (pullbackEqIso (vertex_comp_degreeZero_inv G n)).hom.app (degreeZeroModule G F) ≫
      ObjectProperty.homMk
        (eqToHom (Scheme.QCoh.pullback_obj (G.simplicialScheme.map (op (vertexOp n)))
            (degreeZeroModule G F)) ≫
          stageRestrictModules G (vertexOp n) F)

/-- The last-vertex comparison of `zariskiQCohCounitStage` is an isomorphism. -/
instance zariskiQCohCounitStage_isIso
    (F : SimplicialObject.QCoh G.simplicialScheme) (n : SimplexCategory) :
    IsIso (zariskiQCohCounitStage G F n) :=
  sorry

/-- Underlying sheaf morphism of the counit isomorphism at `F`. -/
def zariskiQCohCounitHom (F : SimplicialObject.QCoh G.simplicialScheme) :
    ((toZariski G).obj ((ofZariski G).obj F)).obj ⟶ F.obj where
  val :=
    { app := fun W ↦
        moduleCatHomOfFun (fun x ↦
          (zariskiQCohCounitStage G F W.unop.base.unop).hom.val.app (op W.unop.opens) x)
      naturality := sorry }

/-- Underlying sheaf morphism of the inverse counit isomorphism at `F`. -/
def zariskiQCohCounitInv (F : SimplicialObject.QCoh G.simplicialScheme) :
    F.obj ⟶ ((toZariski G).obj ((ofZariski G).obj F)).obj where
  val :=
    { app := fun W ↦
        moduleCatHomOfFun (fun x ↦
          (@asIso _ _ _ _
              (zariskiQCohCounitStage G F W.unop.base.unop)
              (zariskiQCohCounitStage_isIso G F W.unop.base.unop)).inv.hom.val.app
            (op W.unop.opens) x)
      naturality := sorry }

/-- The counit isomorphism of the groupoid / Zariski quasi-coherent equivalence, at `F`. -/
def zariskiQCohCounitApp (F : SimplicialObject.QCoh G.simplicialScheme) :
    (ofZariski G ⋙ toZariski G).obj F ≅ F where
  hom := ObjectProperty.homMk (zariskiQCohCounitHom G F)
  inv := ObjectProperty.homMk (zariskiQCohCounitInv G F)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The counit natural isomorphism `ofZariski ⋙ toZariski ≅ 𝟭`. -/
def zariskiQCohCounitIso :
    ofZariski G ⋙ toZariski G ≅ 𝟭 (SimplicialObject.QCoh G.simplicialScheme) :=
  NatIso.ofComponents (fun F ↦ zariskiQCohCounitApp G F) sorry

/-- The category of quasi-coherent modules on a groupoid scheme is equivalent to the
category of quasi-coherent modules on the Zariski site of the associated simplicial scheme. -/
def zariskiQCohEquivalence : G.QCoh ≌ SimplicialObject.QCoh G.simplicialScheme :=
  CategoryTheory.Equivalence.mk (toZariski G) (ofZariski G)
    (zariskiQCohUnitIso G) (zariskiQCohCounitIso G)

/-- The forward functor of `zariskiQCohEquivalence` is `toZariski`. -/
theorem zariskiQCohEquivalence_functor :
    (zariskiQCohEquivalence G).functor = toZariski G :=
  sorry

/-- The inverse functor of `zariskiQCohEquivalence` is `ofZariski`. -/
theorem zariskiQCohEquivalence_inverse :
    (zariskiQCohEquivalence G).inverse = ofZariski G :=
  sorry

end AlgebraicGeometry.GroupoidScheme
