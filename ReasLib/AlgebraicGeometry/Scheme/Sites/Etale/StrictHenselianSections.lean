module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

@[expose] public section

set_option backward.privateInPublic true

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (A : Type w) [Category.{v} A]
variable [HasColimitsOfSize.{u, u + 1} A] [HasColimitsOfSize.{u, u} A]

/-- Evaluation of the étale presheaf's left Kan extension at a scheme over the base. -/
def strictHenselianSections {S X : Scheme.{u}} (p : X ⟶ S) :
    Sheaf S.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf S.smallEtaleTopology A ⋙ (Etale.forget S).op.lan ⋙
    (CategoryTheory.evaluation (Over S)ᵒᵖ A).obj (op (Over.mk p))

/-- Kan-model sections are evaluated on the specified scheme over the base. -/
theorem strictHenselianSections_obj {S X : Scheme.{u}} (p : X ⟶ S)
    (F : Sheaf S.smallEtaleTopology A) :
    (strictHenselianSections A p).obj F =
      ((Etale.forget S).op.leftKanExtension F.obj).obj (op (Over.mk p)) := sorry

/-- Pullback in the Kan-model sections construction is natural in the sheaf. -/
theorem strictHenselianSectionsPullback_naturality {S X Y : Scheme.{u}}
    {p : X ⟶ S} {q : Y ⟶ S} (comparison : Y ⟶ X)
    (comparison_over : comparison ≫ p = q) {F G : Sheaf S.smallEtaleTopology A}
    (morphism : F ⟶ G) :
    (strictHenselianSections A p).map morphism ≫
        ((Etale.forget S).op.leftKanExtension G.obj).map
          (Over.homMk comparison comparison_over).op =
      ((Etale.forget S).op.leftKanExtension F.obj).map
          (Over.homMk comparison comparison_over).op ≫
        (strictHenselianSections A q).map morphism := sorry

/-- Pullback of Kan-model sections is the action of the canonical extension on an
over-base morphism. -/
def strictHenselianSectionsPullback {S X Y : Scheme.{u}} {p : X ⟶ S} {q : Y ⟶ S}
    (comparison : Y ⟶ X) (comparison_over : comparison ≫ p = q) :
    strictHenselianSections A p ⟶ strictHenselianSections A q where
  app F := ((Etale.forget S).op.leftKanExtension F.obj).map
    (Over.homMk comparison comparison_over).op
  naturality := fun _ _ morphism ↦
    strictHenselianSectionsPullback_naturality A comparison comparison_over morphism

/-- Each component of Kan-model sections pullback is the extension's map. -/
theorem strictHenselianSectionsPullback_app {S X Y : Scheme.{u}}
    {p : X ⟶ S} {q : Y ⟶ S} (comparison : Y ⟶ X)
    (comparison_over : comparison ≫ p = q) (F : Sheaf S.smallEtaleTopology A) :
    (strictHenselianSectionsPullback A comparison comparison_over).app F =
      ((Etale.forget S).op.leftKanExtension F.obj).map
        (Over.homMk comparison comparison_over).op := sorry

/-- Composing a lift from a pointed neighborhood with its geometric closed point
gives a point over the base. -/
theorem sectionsToStalkCocone_over {S X : Scheme.{u}} {s : GeometricPoint S}
    {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p)
    (U : CostructuredArrow (Etale.forget S).op (op (Over.mk p))) :
    (neighborhood.closedPoint ≫ U.hom.unop.left) ≫ U.left.unop.hom = s.hom := sorry

/-- The closed-point germs of sections represented on étale objects form a cocone. -/
theorem sectionsToStalkCocone_naturality {S X : Scheme.{u}} {s : GeometricPoint S}
    {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p)
    (F : Sheaf S.smallEtaleTopology A)
    {U V : CostructuredArrow (Etale.forget S).op (op (Over.mk p))} (morphism : U ⟶ V) :
    (CostructuredArrow.proj (Etale.forget S).op (op (Over.mk p)) ⋙ F.obj).map morphism ≫
        s.toSmallEtalePoint.toPresheafFiber V.left.unop
          (Over.homMk (neighborhood.closedPoint ≫ V.hom.unop.left)
            (sectionsToStalkCocone_over neighborhood V)) F.obj =
      s.toSmallEtalePoint.toPresheafFiber U.left.unop
        (Over.homMk (neighborhood.closedPoint ≫ U.hom.unop.left)
          (sectionsToStalkCocone_over neighborhood U)) F.obj ≫ 𝟙 _ := sorry

/-- The cocone of closed-point germs on the diagram representing Kan-model sections. -/
private def sectionsToStalkCocone {S X : Scheme.{u}} {s : GeometricPoint S}
    {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p)
    (F : Sheaf S.smallEtaleTopology A) :
    Cocone (CostructuredArrow.proj (Etale.forget S).op (op (Over.mk p)) ⋙ F.obj) where
  pt := s.toSmallEtalePoint.sheafFiber.obj F
  ι := {
    app := fun U ↦ s.toSmallEtalePoint.toPresheafFiber U.left.unop
      (Over.homMk (neighborhood.closedPoint ≫ U.hom.unop.left)
        (sectionsToStalkCocone_over neighborhood U)) F.obj
    naturality := fun _ _ morphism ↦
      sectionsToStalkCocone_naturality A neighborhood F morphism }

/-- Pulling a neighborhood section along the normalized lift respects germ equivalence. -/
theorem StrictHenselianNeighborhood.stalkSectionsIso_hom_compatible
    {S X : Scheme.{u}} {s : GeometricPoint S} {p : X ⟶ S}
    (neighborhood : StrictHenselianNeighborhood s p) (F : Sheaf S.smallEtaleTopology A)
    {U V : S.Etale} (morphism : U ⟶ V) (point : s.toSmallEtalePoint.fiber.obj U) :
    F.obj.map morphism.op ≫
        ((Etale.forget S).op.leftKanExtensionUnit F.obj).app (op U) ≫
        ((Etale.forget S).op.leftKanExtension F.obj).map (neighborhood.lift U point).op =
      ((Etale.forget S).op.leftKanExtensionUnit F.obj).app (op V) ≫
        ((Etale.forget S).op.leftKanExtension F.obj).map
          (neighborhood.lift V (s.toSmallEtalePoint.fiber.map morphism point)).op := sorry

/-- The map from geometric stalks to Kan-model sections induced by normalized lifts. -/
private def stalkSectionsHom {S X : Scheme.{u}} {s : GeometricPoint S} {p : X ⟶ S}
    (neighborhood : StrictHenselianNeighborhood s p) (F : Sheaf S.smallEtaleTopology A) :
    s.toSmallEtalePoint.sheafFiber.obj F ⟶ (strictHenselianSections A p).obj F :=
  s.toSmallEtalePoint.presheafFiberDesc
    (fun U point ↦ ((Etale.forget S).op.leftKanExtensionUnit F.obj).app (op U) ≫
      ((Etale.forget S).op.leftKanExtension F.obj).map (neighborhood.lift U point).op)
    (fun _ _ morphism point ↦
      neighborhood.stalkSectionsIso_hom_compatible A F morphism point)

/-- The map from Kan-model sections to geometric stalks induced by closed-point germs. -/
private def stalkSectionsInv {S X : Scheme.{u}} {s : GeometricPoint S} {p : X ⟶ S}
    (neighborhood : StrictHenselianNeighborhood s p) (F : Sheaf S.smallEtaleTopology A) :
    (strictHenselianSections A p).obj F ⟶ s.toSmallEtalePoint.sheafFiber.obj F :=
  ((Etale.forget S).op.leftKanExtensionObjIsoColimit F.obj (op (Over.mk p))).hom ≫
    colimit.desc _ (sectionsToStalkCocone A neighborhood F)

/-- Normalized lift followed by the closed-point germ acts identically on stalks. -/
theorem StrictHenselianNeighborhood.stalkSectionsIso_hom_inv_id
    {S X : Scheme.{u}} {s : GeometricPoint S} {p : X ⟶ S}
    (neighborhood : StrictHenselianNeighborhood s p) (F : Sheaf S.smallEtaleTopology A) :
    stalkSectionsHom A neighborhood F ≫ stalkSectionsInv A neighborhood F = 𝟙 _ := sorry

/-- Closed-point germ followed by normalized lift acts identically on Kan-model sections. -/
theorem StrictHenselianNeighborhood.stalkSectionsIso_inv_hom_id
    {S X : Scheme.{u}} {s : GeometricPoint S} {p : X ⟶ S}
    (neighborhood : StrictHenselianNeighborhood s p) (F : Sheaf S.smallEtaleTopology A) :
    stalkSectionsInv A neighborhood F ≫ stalkSectionsHom A neighborhood F = 𝟙 _ := sorry

/-- The normalized-lift comparison is natural in étale sheaves. -/
theorem StrictHenselianNeighborhood.stalkSectionsIso_naturality
    {S X : Scheme.{u}} {s : GeometricPoint S} {p : X ⟶ S}
    (neighborhood : StrictHenselianNeighborhood s p) {F G : Sheaf S.smallEtaleTopology A}
    (morphism : F ⟶ G) :
    s.toSmallEtalePoint.sheafFiber.map morphism ≫ stalkSectionsHom A neighborhood G =
      stalkSectionsHom A neighborhood F ≫ (strictHenselianSections A p).map morphism := sorry

/-- Geometric stalks are canonically identified with Kan-model sections by normalized lifts. -/
def StrictHenselianNeighborhood.stalkSectionsIso {S X : Scheme.{u}}
    {s : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p) :
    s.toSmallEtalePoint.sheafFiber ≅ strictHenselianSections A p :=
  NatIso.ofComponents (fun F ↦ {
    hom := stalkSectionsHom A neighborhood F
    inv := stalkSectionsInv A neighborhood F
    hom_inv_id := neighborhood.stalkSectionsIso_hom_inv_id A F
    inv_hom_id := neighborhood.stalkSectionsIso_inv_hom_id A F })
    (fun morphism ↦ neighborhood.stalkSectionsIso_naturality A morphism)

/-- The stalk-to-sections identification sends a germ to pullback along its normalized lift. -/
theorem StrictHenselianNeighborhood.stalkSectionsIso_germ {S X : Scheme.{u}}
    {s : GeometricPoint S} {p : X ⟶ S} (neighborhood : StrictHenselianNeighborhood s p)
    (F : Sheaf S.smallEtaleTopology A) (U : S.Etale)
    (point : s.toSmallEtalePoint.fiber.obj U) :
    s.toSmallEtalePoint.toPresheafFiber U point F.obj ≫
        (neighborhood.stalkSectionsIso A).hom.app F =
      ((Etale.forget S).op.leftKanExtensionUnit F.obj).app (op U) ≫
        ((Etale.forget S).op.leftKanExtension F.obj).map (neighborhood.lift U point).op := sorry

section GenuineSections

variable [HasProducts.{u} A]
variable [∀ X : Scheme.{u}, HasWeakSheafify X.smallEtaleTopology A]

/-- Evaluation at the identity object of the small étale site. -/
private def identitySections (X : Scheme.{u}) : Sheaf X.smallEtaleTopology A ⥤ A :=
  sheafToPresheaf X.smallEtaleTopology A ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ A).obj
      (op (MorphismProperty.Over.mk _ (𝟙 X) inferInstance))

/-- Genuine sections on a strict henselization evaluate the inverse-image sheaf at
the identity étale object. -/
def strictHenselianGlobalSections {S : Scheme.{u}} (s : GeometricPoint S) :
    Sheaf S.smallEtaleTopology A ⥤ A :=
  (smallEtalePullback (StrictHenselization.toScheme S s)).sheafPullback A
      S.smallEtaleTopology (strictHenselizationAt S s).smallEtaleTopology ⋙
    identitySections A (strictHenselizationAt S s)

/-- The closed-point germ of a genuine strict-henselian section, transported to the
original geometric stalk. -/
private def globalToStalkApp {S : Scheme.{u}} (s : GeometricPoint S)
    (F : Sheaf S.smallEtaleTopology A) :
    (strictHenselianGlobalSections A s).obj F ⟶ s.toSmallEtalePoint.sheafFiber.obj F :=
  let structural := StrictHenselization.toScheme S s
  let geometric := @GeometricPoint.of (strictHenselizationAt S s) s.K inferInstance
    s.isAlgClosed (StrictHenselization.closedPoint s)
  let identityObject : (strictHenselizationAt S s).Etale :=
    MorphismProperty.Over.mk _ (𝟙 _) inferInstance
  let pulled := ((smallEtalePullback structural).sheafPullback A
    S.smallEtaleTopology (strictHenselizationAt S s).smallEtaleTopology).obj F
  let overIso : Over.mk (geometric.hom ≫ structural) ≅ Over.mk s.hom :=
    Over.isoMk (Iso.refl _)
      ((Category.id_comp s.hom).trans (StrictHenselization.closedPoint_over s).symm)
  let fiberTransport := Functor.whiskerLeft (Etale.forget S) (coyoneda.map overIso.inv.op)
  geometric.toSmallEtalePoint.toPresheafFiber identityObject
      (Over.homMk geometric.hom (Category.comp_id geometric.hom)) pulled.obj ≫
    (geometric.toSmallEtalePoint.sheafFiberComapIsoOfMorphismOfSites
      (h_small := smallEtalePullback_fiber_initiallySmall structural s.K geometric.hom)
      (smallEtalePullback structural) A).inv.app F ≫
    (GrothendieckTopology.Point.Hom.sheafFiber
      ⟨smallEtaleInverseImage_comapFiberHom structural geometric⟩).app F ≫
    (GrothendieckTopology.Point.Hom.sheafFiber ⟨fiberTransport⟩).app F

/-- Closed-point germs of genuine sections are natural in the sheaf. -/
theorem strictHenselianGlobalToStalk_naturality {S : Scheme.{u}} (s : GeometricPoint S)
    {F G : Sheaf S.smallEtaleTopology A} (morphism : F ⟶ G) :
    (strictHenselianGlobalSections A s).map morphism ≫ globalToStalkApp A s G =
      globalToStalkApp A s F ≫ s.toSmallEtalePoint.sheafFiber.map morphism := sorry

/-- The natural closed-point germ transformation from genuine sections to geometric stalks. -/
def strictHenselianGlobalToStalk {S : Scheme.{u}} (s : GeometricPoint S) :
    strictHenselianGlobalSections A s ⟶ s.toSmallEtalePoint.sheafFiber where
  app := globalToStalkApp A s
  naturality := fun _ _ morphism ↦ strictHenselianGlobalToStalk_naturality A s morphism

/-- Closed-point germs identify genuine strict-henselian sections with geometric stalks. -/
theorem strictHenselianGlobalToStalk_isIso {S : Scheme.{u}} (s : GeometricPoint S) :
    IsIso (strictHenselianGlobalToStalk A s) := sorry

/-- Genuine inverse-image sections map naturally to their normalized-lift Kan model. -/
def strictHenselianGlobalToSections {S : Scheme.{u}} (s : GeometricPoint S) :
    strictHenselianGlobalSections A s ⟶
      strictHenselianSections A (StrictHenselization.toScheme S s) :=
  strictHenselianGlobalToStalk A s ≫ ((StrictHenselianNeighborhood.canonical s).stalkSectionsIso A).hom

/-- Pullback of genuine sections along an over-base comparison, formed from the
inverse-image adjunction unit and composition of inverse images. -/
private def globalSectionsPullbackApp {S : Scheme.{u}} (s t : GeometricPoint S)
    (comparison : strictHenselizationAt S t ⟶ strictHenselizationAt S s)
    (comparison_over : comparison ≫ StrictHenselization.toScheme S s =
      StrictHenselization.toScheme S t) (F : Sheaf S.smallEtaleTopology A) :
    (strictHenselianGlobalSections A s).obj F ⟶
      (strictHenselianGlobalSections A t).obj F :=
  let sourceMap := StrictHenselization.toScheme S s
  let targetMap := StrictHenselization.toScheme S t
  let sourceScheme := strictHenselizationAt S s
  let targetScheme := strictHenselizationAt S t
  let sourceIdentity : sourceScheme.Etale := MorphismProperty.Over.mk _ (𝟙 _) inferInstance
  let targetIdentity : targetScheme.Etale := MorphismProperty.Over.mk _ (𝟙 _) inferInstance
  let pulled := ((smallEtalePullback sourceMap).sheafPullback A
    S.smallEtaleTopology sourceScheme.smallEtaleTopology).obj F
  let twicePulled := ((smallEtalePullback comparison).sheafPullback A
    sourceScheme.smallEtaleTopology targetScheme.smallEtaleTopology).obj pulled
  let siteIso : smallEtalePullback sourceMap ⋙ smallEtalePullback comparison ≅
      smallEtalePullback (comparison ≫ sourceMap) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) comparison sourceMap).symm
  let compositionIso := Adjunction.leftAdjointCompIso
    ((smallEtalePullback sourceMap).sheafAdjunctionContinuous A
      S.smallEtaleTopology sourceScheme.smallEtaleTopology)
    ((smallEtalePullback comparison).sheafAdjunctionContinuous A
      sourceScheme.smallEtaleTopology targetScheme.smallEtaleTopology)
    ((smallEtalePullback (comparison ≫ sourceMap)).sheafAdjunctionContinuous A
      S.smallEtaleTopology targetScheme.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp' siteIso A S.smallEtaleTopology
      sourceScheme.smallEtaleTopology targetScheme.smallEtaleTopology)
  let overTransport := eqToIso (congrArg (fun structural : targetScheme ⟶ S ↦
    (smallEtalePullback structural).sheafPullback A
      S.smallEtaleTopology targetScheme.smallEtaleTopology) comparison_over)
  let identityLift : targetIdentity ⟶ (smallEtalePullback comparison).obj sourceIdentity :=
    MorphismProperty.Over.homMk
      (pullback.lift comparison (𝟙 targetScheme)
        ((Category.comp_id comparison).trans (Category.id_comp comparison).symm))
      (pullback.lift_snd comparison (𝟙 targetScheme)
        ((Category.comp_id comparison).trans (Category.id_comp comparison).symm))
  (((smallEtalePullback comparison).sheafAdjunctionContinuous A
      sourceScheme.smallEtaleTopology targetScheme.smallEtaleTopology).unit.app pulled).hom.app
      (op sourceIdentity) ≫
    (((smallEtalePullback comparison).sheafPushforwardContinuousCompSheafToPresheafIso A
      sourceScheme.smallEtaleTopology targetScheme.smallEtaleTopology).app twicePulled).hom.app
      (op sourceIdentity) ≫
    twicePulled.obj.map identityLift.op ≫
    ((compositionIso ≪≫ overTransport).hom.app F).hom.app (op targetIdentity)

/-- Genuine sections pullback is natural in the original étale sheaf. -/
theorem strictHenselianGlobalSectionsPullback_naturality {S : Scheme.{u}}
    (s t : GeometricPoint S)
    (comparison : strictHenselizationAt S t ⟶ strictHenselizationAt S s)
    (comparison_over : comparison ≫ StrictHenselization.toScheme S s =
      StrictHenselization.toScheme S t) {F G : Sheaf S.smallEtaleTopology A}
    (morphism : F ⟶ G) :
    (strictHenselianGlobalSections A s).map morphism ≫
        globalSectionsPullbackApp A s t comparison comparison_over G =
      globalSectionsPullbackApp A s t comparison comparison_over F ≫
        (strictHenselianGlobalSections A t).map morphism := sorry

/-- Pullback of genuine strict-henselian sections along an over-base comparison. -/
def strictHenselianGlobalSectionsPullback {S : Scheme.{u}} (s t : GeometricPoint S)
    (comparison : strictHenselizationAt S t ⟶ strictHenselizationAt S s)
    (comparison_over : comparison ≫ StrictHenselization.toScheme S s =
      StrictHenselization.toScheme S t) :
    strictHenselianGlobalSections A s ⟶ strictHenselianGlobalSections A t where
  app := globalSectionsPullbackApp A s t comparison comparison_over
  naturality := fun _ _ morphism ↦
    strictHenselianGlobalSectionsPullback_naturality A s t comparison comparison_over morphism

/-- The comparison between genuine and Kan-model sections intertwines their
independently constructed pullback maps. -/
theorem strictHenselianGlobalToSections_pullback {S : Scheme.{u}}
    (s t : GeometricPoint S)
    (comparison : strictHenselizationAt S t ⟶ strictHenselizationAt S s)
    (comparison_over : comparison ≫ StrictHenselization.toScheme S s =
      StrictHenselization.toScheme S t) :
    strictHenselianGlobalToSections A s ≫
        strictHenselianSectionsPullback A comparison comparison_over =
      strictHenselianGlobalSectionsPullback A s t comparison comparison_over ≫
        strictHenselianGlobalToSections A t := sorry

end GenuineSections

end AlgebraicGeometry.Scheme

end
