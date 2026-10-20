/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.ComplexBaseChange
public import ReasLib.CategoryTheory.InverseSystem.Preorder

/-! Higher direct images of a complex pulled back from one stage of an inverse system. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale

section Pullbacks
variable {I : Type u} [Preorder I] (DX : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T) (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
  (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
  ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable (i0 : I) (K0 : CochainComplex
  (Sheaf (DX.obj (OrderDual.toDual i0)).smallEtaleTopology AddCommGrpCat.{u}) ℤ)

/-- The stage complex is the actual termwise inverse image from the original stage. -/
def pullbackFromBase {i : I} (hi : i0 ≤ i) :
    CochainComplex (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}) ℤ :=
  (transitionPullbackComplex DX hi).obj K0

omit [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
  [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
  [∀ {T U : Scheme.{u}} (f : U ⟶ T) (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G] in
/-- The stage construction evaluates to the canonical complex inverse-image functor. -/
theorem pullbackFromBase_obj {i : I} (hi : i0 ≤ i) :
    pullbackFromBase DX i0 K0 hi = (transitionPullbackComplex DX hi).obj K0 := rfl

/-- The transition between stage complexes is the existing canonical composition comparison. -/
def pullbackFromBase_transition {i j : I} (hi : i0 ≤ i) (hij : i ≤ j) :
    (transitionPullbackComplex DX hij).obj (pullbackFromBase DX i0 K0 hi) ⟶
      pullbackFromBase DX i0 K0 (le_trans hi hij) :=
  (transitionPullbackComplexCompIso DX hi hij).hom.app K0

variable (cX : Cone DX)
variable [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]

/-- The limiting complex is termwise inverse image along the original cone projection. -/
def pullbackFromBaseLimit :
    CochainComplex (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u}) ℤ :=
  ((conePullback DX cX i0).mapHomologicalComplex (ComplexShape.up ℤ)).obj K0

omit [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
  [∀ {T U : Scheme.{u}} (f : U ⟶ T) (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
  [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}] in
/-- Evaluation of the limiting complex as canonical termwise cone inverse image. -/
theorem pullbackFromBaseLimit_obj :
    pullbackFromBaseLimit DX i0 K0 cX =
      ((conePullback DX cX i0).mapHomologicalComplex (ComplexShape.up ℤ)).obj K0 := rfl

/-- The cone comparison is the cochain lift of the existing cone-pullback composition isomorphism. -/
def pullbackFromBaseLimit_transition (i : Set.Ici i0) :
    ((conePullback DX cX i.val).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (pullbackFromBase DX i0 K0 i.property) ⟶
      pullbackFromBaseLimit DX i0 K0 cX :=
  (NatIso.mapHomologicalComplex (conePullbackCompIso DX cX i.property)
    (ComplexShape.up ℤ)).hom.app K0

end Pullbacks

variable {I : Type u} [Preorder I] 
variable (DX DS : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ i : I, IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (DS.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T)
    (G : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {T U : Scheme.{u}} (f : U ⟶ T),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      T.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
variable (g : ∀ i : I, DX.obj (OrderDual.toDual i) ⟶ DS.obj (OrderDual.toDual i))
variable (hg : ∀ {i j : I} (hij : i ≤ j),
    OrderDualInverseSystem.transitionMap DX hij ≫ g i =
      g j ≫ OrderDualInverseSystem.transitionMap DS hij)
variable [∀ i : I,
    ((smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
      (DS.obj (OrderDual.toDual i)).smallEtaleTopology
      (DX.obj (OrderDual.toDual i)).smallEtaleTopology).Additive]
variable [∀ i : I,
    Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived
        ((smallEtalePullback (g i)).sheafPushforwardContinuous AddCommGrpCat.{u}
          (DS.obj (OrderDual.toDual i)).smallEtaleTopology
          (DX.obj (OrderDual.toDual i)).smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (DX.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
variable (cX : Cone DX) (cS : Cone DS)
variable (gX : cX.pt ⟶ cS.pt)
variable (hgX : ∀ i : I,
    cX.π.app (OrderDual.toDual i) ≫ g i = gX ≫ cS.π.app (OrderDual.toDual i))
variable [HasSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cS.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify cX.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
      cS.pt.smallEtaleTopology cX.pt.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (Functor.RightDerived.Cochain.toDerived
      ((smallEtalePullback gX).sheafPushforwardContinuous AddCommGrpCat.{u}
        cS.pt.smallEtaleTopology cX.pt.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf cX.pt.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
variable (i0 : I)
variable (K0 : CochainComplex
    (Sheaf (DX.obj (OrderDual.toDual i0)).smallEtaleTopology AddCommGrpCat.{u}) ℤ)

variable (p : ℤ)


/-- Stage higher direct images are pulled back to the limiting base. -/
def pullbackStageHigherDirectImageComplex (i : Set.Ici i0) :
    Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u} :=
  (conePullback DS cS i.val).obj
    (HigherDirectImage.Complex.value (g i.val) (pullbackFromBase DX i0 K0 i.property) p)

/-- The actual transition is derived base change followed by the canonical complex transition. -/
def higherDirectImageComplex_pullbackDiagramMap (i j : Set.Ici i0) (hij : i.val ≤ j.val) :
    pullbackStageHigherDirectImageComplex DX DS g cS i0 K0 p i ⟶
      pullbackStageHigherDirectImageComplex DX DS g cS i0 K0 p j :=
  (conePullbackCompIso DS cS hij).inv.app _ ≫
    (conePullback DS cS j.val).map
      (HigherDirectImage.Complex.baseChange (g i.val) (g j.val)
        (OrderDualInverseSystem.transitionMap DX hij)
        (OrderDualInverseSystem.transitionMap DS hij) (hg hij)
        (pullbackFromBase DX i0 K0 i.property) p ≫
      HigherDirectImage.Complex.map (g j.val)
        (pullbackFromBase_transition DX i0 K0 i.property hij) p)

/-- The transition at a reflexive index is the identity morphism. -/
theorem higherDirectImageComplex_pullbackDiagramMap_id (i : Set.Ici i0) :
    higherDirectImageComplex_pullbackDiagramMap DX DS g hg cS i0 K0 p i i (le_refl i.val) =
      𝟙 (pullbackStageHigherDirectImageComplex DX DS g cS i0 K0 p i) := sorry

/-- Successive canonical transitions compose through an intermediate index. -/
theorem higherDirectImageComplex_pullbackDiagramMap_comp (i j k : Set.Ici i0)
    (hij : i.val ≤ j.val) (hjk : j.val ≤ k.val) :
    higherDirectImageComplex_pullbackDiagramMap DX DS g hg cS i0 K0 p i k (le_trans hij hjk) =
      higherDirectImageComplex_pullbackDiagramMap DX DS g hg cS i0 K0 p i j hij ≫
        higherDirectImageComplex_pullbackDiagramMap DX DS g hg cS i0 K0 p j k hjk := sorry

/-- The ordinary directed upper-tail diagram of pulled-back higher direct images. -/
def higherDirectImageComplex_pullbackDiagram :
    Set.Ici i0 ⥤ Sheaf cS.pt.smallEtaleTopology AddCommGrpCat.{u} where
  obj := pullbackStageHigherDirectImageComplex DX DS g cS i0 K0 p
  map {i j} f := higherDirectImageComplex_pullbackDiagramMap DX DS g hg cS i0 K0 p i j (leOfHom f)
  map_id := higherDirectImageComplex_pullbackDiagramMap_id DX DS g hg cS i0 K0 p
  map_comp f h := higherDirectImageComplex_pullbackDiagramMap_comp DX DS g hg cS i0 K0 p _ _ _ (leOfHom f) (leOfHom h)

/-- Evaluation of the upper-tail diagram recovers its specified stage sheaf. -/
theorem higherDirectImageComplex_pullbackDiagram_obj (i : Set.Ici i0) :
    (higherDirectImageComplex_pullbackDiagram DX DS g hg cS i0 K0 p).obj i =
      pullbackStageHigherDirectImageComplex DX DS g cS i0 K0 p i := rfl

/-- The stage arrow to the limit is constructed from the same canonical base-change map. -/
def higherDirectImageComplex_pullbackStageMap (i : Set.Ici i0) :
    pullbackStageHigherDirectImageComplex DX DS g cS i0 K0 p i ⟶
      HigherDirectImage.Complex.value gX (pullbackFromBaseLimit DX i0 K0 cX) p :=
  HigherDirectImage.Complex.baseChange (g i.val) gX
    (cX.π.app (OrderDual.toDual i.val)) (cS.π.app (OrderDual.toDual i.val))
    (hgX i.val) (pullbackFromBase DX i0 K0 i.property) p ≫
      HigherDirectImage.Complex.map gX (pullbackFromBaseLimit_transition DX i0 K0 cX i) p

/-- Stage arrows to the limit respect every transition in the upper-tail diagram. -/
theorem higherDirectImageComplex_pullbackStageMap_naturality (i j : Set.Ici i0)
    (hij : i.val ≤ j.val) :
    higherDirectImageComplex_pullbackDiagramMap DX DS g hg cS i0 K0 p i j hij ≫
      higherDirectImageComplex_pullbackStageMap DX DS g cX cS gX hgX i0 K0 p j =
        higherDirectImageComplex_pullbackStageMap DX DS g cX cS gX hgX i0 K0 p i := sorry

/-- The canonical comparison cocone on the upper-tail diagram. -/
def higherDirectImageComplex_pullbackCocone :
    Cocone (higherDirectImageComplex_pullbackDiagram DX DS g hg cS i0 K0 p) where
  pt := HigherDirectImage.Complex.value gX (pullbackFromBaseLimit DX i0 K0 cX) p
  ι :=
    { app := higherDirectImageComplex_pullbackStageMap DX DS g cX cS gX hgX i0 K0 p
      naturality := fun i j f =>
        (higherDirectImageComplex_pullbackStageMap_naturality DX DS g hg cX cS gX hgX i0 K0 p i j (leOfHom f)).trans
          (Category.comp_id _).symm }

variable [HasColimit (higherDirectImageComplex_pullbackDiagram DX DS g hg cS i0 K0 p)]

/-- The map from the colimit is the universal descent of the specified stage maps. -/
def higherDirectImageComplex_pullbackComparison :
    colimit (higherDirectImageComplex_pullbackDiagram DX DS g hg cS i0 K0 p) ⟶
      HigherDirectImage.Complex.value gX (pullbackFromBaseLimit DX i0 K0 cX) p :=
  colimit.desc (higherDirectImageComplex_pullbackDiagram DX DS g hg cS i0 K0 p)
    (higherDirectImageComplex_pullbackCocone DX DS g hg cX cS gX hgX i0 K0 p)

/-- The universal colimit comparison restricts to the specified stage arrow. -/
theorem higherDirectImageComplex_pullbackComparison_ι (i : Set.Ici i0) :
    colimit.ι (higherDirectImageComplex_pullbackDiagram DX DS g hg cS i0 K0 p) i ≫
      higherDirectImageComplex_pullbackComparison DX DS g hg cX cS gX hgX i0 K0 p =
        higherDirectImageComplex_pullbackStageMap DX DS g cX cS gX hgX i0 K0 p i :=
  colimit.ι_desc (higherDirectImageComplex_pullbackCocone DX DS g hg cX cS gX hgX i0 K0 p) i

/-- Uniform cohomological boundedness at the original stage gives the comparison isomorphism. -/
theorem higherDirectImageComplex_colimit_pullback
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap DX hij)]
    [∀ {i j : I} (hij : i ≤ j), IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    [∀ i : I, QuasiCompact (g i)] [∀ i : I, QuasiSeparated (g i)]
    [QuasiCompact gX] [QuasiSeparated gX]
    [Nonempty I] [IsDirected I (· ≤ ·)]
    (hcX : IsLimit cX) (hcS : IsLimit cS) (a : ℤ) (hK : K0.IsGE a) :
    IsIso (higherDirectImageComplex_pullbackComparison DX DS g hg cX cS gX hgX i0 K0 p) := sorry

end AlgebraicGeometry.Scheme.Etale
