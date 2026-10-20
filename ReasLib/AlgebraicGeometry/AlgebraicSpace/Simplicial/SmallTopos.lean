module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.SmallSheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.RingedSite
public import ReasLib.CategoryTheory.Sites.Simplicial.SheafSystem
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.EssentiallySmall

/-! # Small-coefficient total topoi and their augmentations -/

set_option backward.privateInPublic true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialSites
open CategoryTheory.SimplicialObject
open AlgebraicGeometry.AlgebraicSpace.Fppf.AffineCoverBasis
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial.SmallCoefficients

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- A coded chart is inserted in the same degree as the object it covers. -/
private def totalChart (Y : sliceTotalSite U) (c : ChartCode Y.fiber.left) : sliceTotalSite U :=
  (Grothendieck.ι (sliceDiagram U) Y.base).obj (overChart Y.fiber c)

/-- The covering arrow of a coded chart has identity simplicial degree. -/
private def totalChartMap (Y : sliceTotalSite U) (c : ChartCode Y.fiber.left) :
    totalChart U Y c ⟶ Y :=
  (Grothendieck.ι (sliceDiagram U) Y.base).map (overChartMap Y.fiber c)

/-- The underlying covering morphism is the coded chart morphism. -/
private theorem totalChartMap_left (Y : sliceTotalSite U) (c : ChartCode Y.fiber.left) :
    (totalChartMap U Y c).fiber.left = (chart c).hom := by
  change (eqToHom _ ≫ overChartMap Y.fiber c).left = _
  rw [Over.comp_left, Over.eqToHom_left]
  change 𝟙 _ ≫ (chart c).hom = _
  exact Category.id_comp _

/-- A coded factorization gives the actual chart morphism over the degree map of a total arrow. -/
private def totalLiftMap {Y Z : sliceTotalSite U} (f : Y ⟶ Z)
    {d : ChartCode Y.fiber.left} {c : ChartCode Z.fiber.left}
    (l : Lift f.fiber.left d c) : totalChart U Y d ⟶ totalChart U Z c where
  base := f.base
  fiber := Over.homMk (liftMap (f := f.fiber.left) l) (by
    change liftMap (f := f.fiber.left) l ≫ ((chart c).hom ≫ Z.fiber.hom) =
      ((chart d).hom ≫ Y.fiber.hom) ≫ U.map f.base
    rw [← Category.assoc, liftMap_w, Category.assoc, Over.w f.fiber, Category.assoc]
    rfl)

/-- Underlying maps of total arrows compose without changing their carriers. -/
private theorem totalFiber_comp_left {Y Z W : sliceTotalSite U}
    (f : Y ⟶ Z) (g : Z ⟶ W) :
    (f ≫ g).fiber.left = f.fiber.left ≫ g.fiber.left := by
  change (eqToHom _ ≫ (Over.map (U.map g.base)).map f.fiber ≫ g.fiber).left = _
  simp only [Over.comp_left, Over.eqToHom_left, Over.map_map_left,
    eqToHom_refl, Category.id_comp]
  change 𝟙 Y.fiber.left ≫ f.fiber.left ≫ g.fiber.left = _
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- A lifted chart morphism has the prescribed composite to the covered object. -/
private theorem totalLiftMap_w {Y Z : sliceTotalSite U} (f : Y ⟶ Z)
    {d : ChartCode Y.fiber.left} {c : ChartCode Z.fiber.left}
    (l : Lift f.fiber.left d c) :
    totalLiftMap U f l ≫ totalChartMap U Z c = totalChartMap U Y d ≫ f := by
  dsimp only [totalChart] at *
  apply Grothendieck.ext _ _ (by
    change f.base ≫ 𝟙 Z.base = 𝟙 Y.base ≫ f.base
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  apply Over.OverMorphism.ext
  change (eqToHom _ ≫ (totalLiftMap U f l ≫ totalChartMap U Z c).fiber).left = _
  rw [Over.comp_left, Over.eqToHom_left]
  change 𝟙 _ ≫ (totalLiftMap U f l ≫ totalChartMap U Z c).fiber.left = _
  rw [Category.id_comp]
  rw [totalFiber_comp_left, totalFiber_comp_left]
  rw [totalChartMap_left, totalChartMap_left]
  exact liftMap_w (S := S) (X := Z.fiber.left) (Y := Y.fiber.left)
    (f := f.fiber.left) (d := d) (c := c) l

/-- A matching family agrees on every common cone of its covering chart arrows. -/
private def TotalMatching (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u)
    {Y : sliceTotalSite U} (B : Cover Y.fiber.left) : Type u :=
  {s : ∀ c : B.val, P.obj (op (totalChart U Y c.val)) //
    ∀ (b c : B.val) (W : sliceTotalSite U)
      (f : W ⟶ totalChart U Y b.val) (g : W ⟶ totalChart U Y c.val),
      f ≫ totalChartMap U Y b.val = g ≫ totalChartMap U Y c.val →
        P.map f.op (s b) = P.map g.op (s c)}

/-- Agreement in total Plus means equality after a further covering refinement in the fixed degree. -/
private def totalPlusRel (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) (Y : sliceTotalSite U)
    (s t : Σ B : Cover Y.fiber.left, TotalMatching U P B) : Prop :=
  ∃ D : Cover Y.fiber.left,
    (∀ d : D.val, ∃ b : s.1.val, Nonempty (Lift (𝟙 Y.fiber.left) d.val b.val)) ∧
    (∀ d : D.val, ∃ c : t.1.val, Nonempty (Lift (𝟙 Y.fiber.left) d.val c.val)) ∧
    ∀ (d : D.val) (b : s.1.val) (c : t.1.val)
      (l : Lift (𝟙 Y.fiber.left) d.val b.val) (k : Lift (𝟙 Y.fiber.left) d.val c.val),
      P.map ((Grothendieck.ι (sliceDiagram U) Y.base).map
        (overLiftMap (𝟙 Y.fiber) l)).op (s.2.val b) =
        P.map ((Grothendieck.ι (sliceDiagram U) Y.base).map
          (overLiftMap (𝟙 Y.fiber) k)).op (t.2.val c)

/-- All qualifying lifts determine one restriction value, independently of the lift. -/
private theorem totalRestrictionValue_existsUnique (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u)
    {Y Z : sliceTotalSite U} (f : Y ⟶ Z) {B : Cover Z.fiber.left}
    (s : TotalMatching U P B) (d : (pullbackCover f.fiber.left B).val) :
    ∃! x : P.obj (op (totalChart U Y d.val)),
      ∀ (b : B.val) (l : Lift f.fiber.left d.val b.val),
        P.map (totalLiftMap U f l).op (s.val b) = x := by
  obtain ⟨b, ⟨l⟩⟩ := d.property
  refine ⟨P.map (totalLiftMap U f l).op (s.val b), ?_, ?_⟩
  · intro c k
    apply s.property c b _ (totalLiftMap U f k) (totalLiftMap U f l)
    rw [totalLiftMap_w, totalLiftMap_w]
  · intro x hx
    exact (hx b l).symm

/-- The restriction value is extracted from its proved unique characterization. -/
private def totalRestrictionValue (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u)
    {Y Z : sliceTotalSite U} (f : Y ⟶ Z) {B : Cover Z.fiber.left}
    (s : TotalMatching U P B) (d : (pullbackCover f.fiber.left B).val) :
    P.obj (op (totalChart U Y d.val)) :=
  (totalRestrictionValue_existsUnique U P f s d).choose

/-- Restriction of a matching family uses all coded factorizations of the total arrow. -/
private def totalRestrictMatching (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u)
    {Y Z : sliceTotalSite U} (f : Y ⟶ Z) {B : Cover Z.fiber.left}
    (s : TotalMatching U P B) : TotalMatching U P (pullbackCover f.fiber.left B) :=
  ⟨totalRestrictionValue U P f s, by
    intro d e W g h w
    obtain ⟨b, ⟨l⟩⟩ := d.property
    obtain ⟨c, ⟨k⟩⟩ := e.property
    dsimp only [totalRestrictionValue]
    rw [← (totalRestrictionValue_existsUnique U P f s d).choose_spec.1 b l,
      ← (totalRestrictionValue_existsUnique U P f s e).choose_spec.1 c k]
    simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]
    apply s.property b c
    simp only [Category.assoc, totalLiftMap_w]
    rw [← Category.assoc, w, Category.assoc]⟩

/-- Pullback acts on the disjoint union of matching families over all small covers. -/
private def totalRestrictRepresentative (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u)
    {V W : sliceTotalSite U} (f : V ⟶ W) (s : Σ B : Cover W.fiber.left, TotalMatching U P B) :
    Σ B : Cover V.fiber.left, TotalMatching U P B :=
  ⟨pullbackCover f.fiber.left s.1, totalRestrictMatching U P f s.2⟩

/-- A presheaf morphism acts on total matching families by its component maps. -/
private def totalMapMatching {P Q : (sliceTotalSite U)ᵒᵖ ⥤ Type u} (α : P ⟶ Q)
    {V : sliceTotalSite U} {B : Cover V.fiber.left} (s : TotalMatching U P B) : TotalMatching U Q B :=
  ⟨fun c ↦ α.app _ (s.val c), by
    intro b c W f g w
    exact (ConcreteCategory.congr_hom (α.naturality f.op) (s.val b)).symm.trans
      ((congrArg (α.app _) (s.property b c W f g w)).trans
        (ConcreteCategory.congr_hom (α.naturality g.op) (s.val c)))⟩

/-- A total section restricts to every coded chart in its degree. -/
private def totalUnitRepresentative (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) (V : sliceTotalSite U)
    (x : P.obj (op V)) : Σ B : Cover V.fiber.left, TotalMatching U P B :=
  ⟨allCharts V.fiber.left, ⟨fun c ↦ P.map (totalChartMap U V c.val).op x, by
    intro b c W f g w
    simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, w]⟩⟩

/-- Refinement equivalence is compatible with restriction, presheaf morphisms, and the section unit. -/
private abbrev TotalPlusLaws : Prop :=
    (∀ (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) (V : sliceTotalSite U), Equivalence (totalPlusRel U P V)) ∧
    (∀ (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) {V W : sliceTotalSite U} (f : V ⟶ W)
      (s t : Σ B : Cover W.fiber.left, TotalMatching U P B), totalPlusRel U P W s t →
        totalPlusRel U P V (totalRestrictRepresentative U P f s) (totalRestrictRepresentative U P f t)) ∧
    (∀ (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) (V : sliceTotalSite U) (s : Σ B : Cover V.fiber.left, TotalMatching U P B),
      totalPlusRel U P V (totalRestrictRepresentative U P (𝟙 V) s) s) ∧
    (∀ (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) {V W Z : sliceTotalSite U} (f : V ⟶ W) (g : W ⟶ Z)
      (s : Σ B : Cover Z.fiber.left, TotalMatching U P B),
      totalPlusRel U P V (totalRestrictRepresentative U P (f ≫ g) s)
        (totalRestrictRepresentative U P f (totalRestrictRepresentative U P g s))) ∧
    (∀ {P Q : (sliceTotalSite U)ᵒᵖ ⥤ Type u} (α : P ⟶ Q) (V : sliceTotalSite U)
      (s t : Σ B : Cover V.fiber.left, TotalMatching U P B), totalPlusRel U P V s t →
        totalPlusRel U Q V ⟨s.1, totalMapMatching U α s.2⟩ ⟨t.1, totalMapMatching U α t.2⟩) ∧
    (∀ (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) {V W : sliceTotalSite U} (f : V ⟶ W) (x : P.obj (op W)),
      totalPlusRel U P V (totalRestrictRepresentative U P f (totalUnitRepresentative U P W x))
        (totalUnitRepresentative U P V (P.map f.op x)))


/-- The quotient of small matching families by agreement on a covering refinement. -/
private def TotalPlus (h : TotalPlusLaws U) (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) (V : sliceTotalSite U) : Type u :=
  Quotient ⟨totalPlusRel U P V, h.1 P V⟩

/-- Restriction in the matching-family quotient is induced by all-factorization pullback. -/
private def totalPlusRestriction (h : TotalPlusLaws U) (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) {V W : sliceTotalSite U}
    (f : V ⟶ W) : TotalPlus U h P W → TotalPlus U h P V :=
  Quotient.map (totalRestrictRepresentative U P f) (h.2.1 P f)

/-- The matching-family quotient is a presheaf with values in the original universe. -/
private def totalPlusObj (h : TotalPlusLaws U) (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) : (sliceTotalSite U)ᵒᵖ ⥤ Type u where
  obj V := TotalPlus U h P V.unop
  map f := ↾(totalPlusRestriction U h P f.unop)
  map_id V := by
    ext x
    refine Quotient.inductionOn x ?_
    intro s
    exact Quotient.sound (h.2.2.1 P V.unop s)
  map_comp f g := by
    ext x
    refine Quotient.inductionOn x ?_
    intro s
    exact Quotient.sound (h.2.2.2.1 P g.unop f.unop s)

/-- The unit sends a section to its restrictions on every affine chart. -/
private def totalToPlus (h : TotalPlusLaws U) (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) : P ⟶ totalPlusObj U h P where
  app V := ↾fun x ↦ Quotient.mk _ (totalUnitRepresentative U P V.unop x)
  naturality {V W} f := by
    ext x
    exact (Quotient.sound (h.2.2.2.2.2 P f.unop x)).symm

/-- A presheaf morphism acts on the matching-family quotient by its component maps. -/
private def totalPlusMap (h : TotalPlusLaws U) {P Q : (sliceTotalSite U)ᵒᵖ ⥤ Type u} (α : P ⟶ Q) : totalPlusObj U h P ⟶ totalPlusObj U h Q where
  app V := ↾(Quotient.map (fun s ↦ ⟨s.1, totalMapMatching U α s.2⟩)
    (h.2.2.2.2.1 α V.unop))
  naturality {V W} f := by
    ext x
    refine Quotient.inductionOn x ?_
    intro s
    apply congrArg (Quotient.mk _)
    apply congrArg (Sigma.mk (pullbackCover f.unop.fiber.left s.1))
    apply Subtype.ext
    funext d
    obtain ⟨b, ⟨l⟩⟩ := d.property
    change α.app _ (totalRestrictionValue U P f.unop s.2 d) =
      totalRestrictionValue U Q f.unop (totalMapMatching U α s.2) d
    dsimp only [totalRestrictionValue]
    rw [← (totalRestrictionValue_existsUnique U P f.unop s.2 d).choose_spec.1 b l,
      ← (totalRestrictionValue_existsUnique U Q f.unop (totalMapMatching U α s.2) d).choose_spec.1 b l]
    exact ConcreteCategory.congr_hom (α.naturality (totalLiftMap U f.unop l).op) (s.2.val b)

/-- Taking matching-family quotients is functorial in the presheaf. -/
private def totalPlusFunctor (h : TotalPlusLaws U) : ((sliceTotalSite U)ᵒᵖ ⥤ Type u) ⥤ ((sliceTotalSite U)ᵒᵖ ⥤ Type u) where
  obj := totalPlusObj U h
  map := totalPlusMap U h
  map_id P := by
    ext V x
    refine Quotient.inductionOn x ?_
    intro s
    rfl
  map_comp α β := by
    ext V x
    refine Quotient.inductionOn x ?_
    intro s
    rfl

/-- The coded chart family covers in the total topology. -/
private abbrev TotalChartCoverLaw : Prop :=
  ∀ (V : sliceTotalSite U) (B : Cover V.fiber.left),
    Sieve.ofArrows (fun c : B.val ↦ totalChart U V c.val)
      (fun c ↦ totalChartMap U V c.val) ∈ sliceTotalTopology (fppfTopology S) U V

/-- The fixed-degree matching-family quotient is functorial, and its double application is a sheaf. -/
theorem totalFppfPlus_laws : TotalPlusLaws U ∧
    (∀ (h : TotalPlusLaws U) (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u),
      Presheaf.IsSheaf (sliceTotalTopology (fppfTopology S) U)
        (totalPlusObj U h (totalPlusObj U h P))) ∧ TotalChartCoverLaw U := by
  sorry

/-- The total fppf sheafification has the explicit twofold matching-family quotient as its presheaf. -/
def totalFppfSheafification :
    ((sliceTotalSite U)ᵒᵖ ⥤ Type u) ⥤ Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u) where
  obj P := ⟨totalPlusObj U (totalFppfPlus_laws U).1
    (totalPlusObj U (totalFppfPlus_laws U).1 P),
      (totalFppfPlus_laws U).2.1 _ P⟩
  map α := ObjectProperty.homMk
    (totalPlusMap U (totalFppfPlus_laws U).1 (totalPlusMap U (totalFppfPlus_laws U).1 α))
  map_id P := by
    apply ObjectProperty.hom_ext
    exact (totalPlusFunctor U (totalFppfPlus_laws U).1 ⋙
      totalPlusFunctor U (totalFppfPlus_laws U).1).map_id P
  map_comp α β := by
    apply ObjectProperty.hom_ext
    exact (totalPlusFunctor U (totalFppfPlus_laws U).1 ⋙
      totalPlusFunctor U (totalFppfPlus_laws U).1).map_comp α β

/-- The totalFppfSheafification U unit is the composite of the two restriction-family units. -/
def totalFppfSheafificationUnit (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) :
    P ⟶ ((totalFppfSheafification U).obj P).obj :=
  totalToPlus U (totalFppfPlus_laws U).1 P ≫ totalToPlus U (totalFppfPlus_laws U).1 (totalPlusObj U (totalFppfPlus_laws U).1 P)

/-- Amalgamate a matching family after applying a presheaf morphism to a sheaf. -/
private def totalAmalgamateMatching {P : (sliceTotalSite U)ᵒᵖ ⥤ Type u}
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)) (α : P ⟶ F.obj)
    {V : sliceTotalSite U} {B : Cover V.fiber.left} (s : TotalMatching U P B) : F.obj.obj (op V) :=
  (F.property.amalgamateOfArrows (fun c : B.val ↦ totalChartMap U V c.val)
    ((totalFppfPlus_laws U).2.2 V B)
    (fun c ↦ (↾fun _ : PUnit.{u + 1} ↦ α.app _ (s.val c)))
    (by
      intro W b c f g h
      ext x
      have e := s.property b c W f g h
      exact (ConcreteCategory.congr_hom (α.naturality f.op) (s.val b)).symm.trans
        ((congrArg (α.app _) e).trans
          (ConcreteCategory.congr_hom (α.naturality g.op) (s.val c))))) PUnit.unit

/-- Unique amalgamation is independent of refinement and commutes with restriction. -/
private def TotalGluingLaws : Prop :=
  (∀ {P : (sliceTotalSite U)ᵒᵖ ⥤ Type u} (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (α : P ⟶ F.obj) (V : sliceTotalSite U) (s t : Σ B : Cover V.fiber.left, TotalMatching U P B),
    totalPlusRel U P V s t → totalAmalgamateMatching U F α s.2 = totalAmalgamateMatching U F α t.2) ∧
  (∀ {P : (sliceTotalSite U)ᵒᵖ ⥤ Type u} (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (α : P ⟶ F.obj) {V W : sliceTotalSite U} (f : V ⟶ W)
    (s : Σ B : Cover W.fiber.left, TotalMatching U P B),
    totalAmalgamateMatching U F α (totalRestrictRepresentative U P f s).2 =
      F.obj.map f.op (totalAmalgamateMatching U F α s.2))

/-- Extension to the matching-family quotient uses the target sheaf's unique amalgamation. -/
private def totalPlusLift (h : TotalGluingLaws U) {P : (sliceTotalSite U)ᵒᵖ ⥤ Type u}
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)) (α : P ⟶ F.obj) : totalPlusObj U (totalFppfPlus_laws U).1 P ⟶ F.obj where
  app V := ↾(Quotient.lift (fun s ↦ totalAmalgamateMatching U F α s.2) (h.1 F α V.unop))
  naturality {V W} f := by
    ext x
    refine Quotient.inductionOn x ?_
    intro s
    exact h.2 F α f.unop s

/-- A map from a presheaf to a sheaf extends by amalgamating the two successive matching families. -/
private def totalFppfSheafificationHomInv (h : TotalGluingLaws U)
    (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (α : P ⟶ F.obj) : (totalFppfSheafification U).obj P ⟶ F :=
  ObjectProperty.homMk (totalPlusLift U h F (totalPlusLift U h F α))

/-- Restriction along the twofold matching-family unit gives the forward adjunction map. -/
private def totalFppfSheafificationHomTo (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u)
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)) (α : (totalFppfSheafification U).obj P ⟶ F) : P ⟶ F.obj :=
  totalFppfSheafificationUnit U P ≫ α.hom

/-- Two successive unique amalgamations give the natural Hom equivalence of totalFppfSheafification U. -/
theorem totalFppfSheafification_adjunction_laws :
    TotalGluingLaws U ∧ ∀ h : TotalGluingLaws U,
    (∀ (P : (sliceTotalSite U)ᵒᵖ ⥤ Type u) (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)),
      Function.LeftInverse (totalFppfSheafificationHomInv U h P F) (totalFppfSheafificationHomTo U P F) ∧
      Function.RightInverse (totalFppfSheafificationHomInv U h P F) (totalFppfSheafificationHomTo U P F)) ∧
    (∀ {P Q : (sliceTotalSite U)ᵒᵖ ⥤ Type u} {F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)}
      (α : P ⟶ Q) (β : Q ⟶ F.obj),
      totalFppfSheafificationHomInv U h P F (α ≫ β) =
        (totalFppfSheafification U).map α ≫ totalFppfSheafificationHomInv U h Q F β) ∧
    (∀ {P : (sliceTotalSite U)ᵒᵖ ⥤ Type u} {F G : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)}
      (α : (totalFppfSheafification U).obj P ⟶ F) (β : F ⟶ G),
      totalFppfSheafificationHomTo U P G (α ≫ β) = totalFppfSheafificationHomTo U P F α ≫ β.hom) := by
  sorry

/-- The adjunction uses the explicit unit and successive unique amalgamations. -/
def totalFppfSheafificationAdjunction : totalFppfSheafification U  ⊣ sheafToPresheaf (sliceTotalTopology (fppfTopology S) U) (Type u) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P F ↦
        { toFun := totalFppfSheafificationHomTo U P F
          invFun := totalFppfSheafificationHomInv U (totalFppfSheafification_adjunction_laws U ).1 P F
          left_inv := (((totalFppfSheafification_adjunction_laws U ).2
            (totalFppfSheafification_adjunction_laws U ).1).1 P F).1
          right_inv := (((totalFppfSheafification_adjunction_laws U ).2
            (totalFppfSheafification_adjunction_laws U ).1).1 P F).2 }
      homEquiv_naturality_left_symm := ((totalFppfSheafification_adjunction_laws U ).2
        (totalFppfSheafification_adjunction_laws U ).1).2.1
      homEquiv_naturality_right := ((totalFppfSheafification_adjunction_laws U ).2
        (totalFppfSheafification_adjunction_laws U ).1).2.2 }

/-- The twofold matching-family totalFppfSheafification U preserves finite limits. -/
theorem totalFppfSheafification_preservesFiniteLimits :
    PreservesFiniteLimits (totalFppfSheafification U ) := by
  sorry

/-- A total étale arrow is determined by its simplex operator and its underlying algebraic-space map. -/
private instance totalEtaleLocallySmall : LocallySmall.{u} (SpacesEtale U) where
  hom_small Y Z := small_of_injective
    (f := fun f : Y ⟶ Z ↦
      (f.simplex, equivShrink.{u} (Y.obj.left ⟶ Z.obj.left) f.hom)) (by
        intro f g e
        cases f with
        | mk φ f w =>
          cases g with
          | mk ψ g v =>
            have e₁ := congrArg Prod.fst e
            have e₂ := (equivShrink (Y.obj.left ⟶ Z.obj.left)).injective (congrArg Prod.snd e)
            cases e₁
            cases e₂
            rfl)

set_option backward.isDefEq.respectTransparency false in
/-- A total slice arrow is determined by its degree map and its underlying algebraic-space map. -/
private instance totalFppfLocallySmall : LocallySmall.{u} (sliceTotalSite U) where
  hom_small Y Z := small_of_injective
    (f := fun f : Y ⟶ Z ↦
      (f.base, equivShrink.{u} (Y.fiber.left ⟶ Z.fiber.left) f.fiber.left)) (by
        intro f g e
        apply Grothendieck.ext _ _ (congrArg Prod.fst e)
        apply Over.OverMorphism.ext
        change (eqToHom _ ≫ f.fiber).left = g.fiber.left
        rw [Over.comp_left, Over.eqToHom_left]
        change 𝟙 _ ≫ f.fiber.left = g.fiber.left
        exact (Category.id_comp _).trans
          ((equivShrink (Y.fiber.left ⟶ Z.fiber.left)).injective (congrArg Prod.snd e)))

/-- The small family of étale charts consists of a simplicial degree and a chart in that degree. -/
private def TotalChartObjects : Type u :=
  Σ n : SimplexCategoryᵒᵖ, SmallEtale.AtlasCharts.Site (U.obj n)

/-- A degree and a small chart determine the corresponding total étale object. -/
private def totalChartObject (c : TotalChartObjects U) : SpacesEtale U :=
  SpacesEtale.ofStage c.1 ((SpacesEtale.AtlasCharts.inclusion (U.obj c.1)).obj c.2)

/-- The full chart category inherits the small Hom bound from total étale arrows. -/
private instance totalChartLocallySmall :
    LocallySmall.{u} (InducedCategory (SpacesEtale U) (totalChartObject U)) :=
  locallySmall_of_faithful (inducedFunctor (totalChartObject U))

/-- The full category of the small total chart family, with small Hom models. -/
private def TotalChartSite : Cat.{u, u} :=
  Cat.of (ShrinkHoms (InducedCategory (SpacesEtale U) (totalChartObject U)))

/-- The total chart inclusion forgets only the small Hom model. -/
private def totalChartInclusion : TotalChartSite U ⥤ SpacesEtale U :=
  ShrinkHoms.inverse (InducedCategory (SpacesEtale U) (totalChartObject U)) ⋙
    inducedFunctor (totalChartObject U)

/-- Every arrow between total charts is represented in their full small category. -/
private instance totalChartInclusionFull : (totalChartInclusion U).Full where
  map_surjective {X Y} f := by
    let g : (ShrinkHoms.inverse.{u} (InducedCategory (SpacesEtale U) (totalChartObject U))).obj X ⟶
        (ShrinkHoms.inverse.{u} (InducedCategory (SpacesEtale U) (totalChartObject U))).obj Y :=
      InducedCategory.homMk f
    exact ⟨equivShrink.{u} _ g, by
      change ((equivShrink.{u} _).symm (equivShrink.{u} _ g)).hom = f
      rw [Equiv.symm_apply_apply]
      rfl⟩

/-- The total chart inclusion into the fppf total category retains the actual chart object. -/
private def totalChartBigInclusion : TotalChartSite U ⥤ sliceTotalSite U :=
  totalChartInclusion U ⋙ toSliceTotal U

/-- Every total étale object is covered by the small charts in its degree. -/
instance totalChartInclusion_dense :
    (totalChartInclusion U).IsCoverDense (spacesEtaleTotalTopology U) := by
  sorry

/-- A left-extension generator records a chart, an actual small-model arrow to it, and a section. -/
private def TotalChartGenerator (P : (SpacesEtale U)ᵒᵖ ⥤ Type u) (V : sliceTotalSite U) : Type u :=
  Σ c : TotalChartSite U,
    Shrink.{u} (V ⟶ (totalChartBigInclusion U).obj c) ×
      P.obj (op ((totalChartInclusion U).obj c))

/-- The coend relation identifies restriction of a section with postcomposition of its chart arrow. -/
private def totalChartRelation (P : (SpacesEtale U)ᵒᵖ ⥤ Type u) (V : sliceTotalSite U)
    (s t : TotalChartGenerator U P V) : Prop :=
  ∃ (c d : TotalChartSite U) (h : c ⟶ d)
    (f : V ⟶ (totalChartBigInclusion U).obj c)
    (x : P.obj (op ((totalChartInclusion U).obj d))),
    s = ⟨c, (equivShrink _ f, P.map ((totalChartInclusion U).map h).op x)⟩ ∧
    t = ⟨d, (equivShrink _ (f ≫ (totalChartBigInclusion U).map h), x)⟩

/-- The left-extension section carrier is the small quotient by the contravariant coend relation. -/
private def totalChartExtensionValue (P : (SpacesEtale U)ᵒᵖ ⥤ Type u) (V : sliceTotalSite U) : Type u :=
  Quot (totalChartRelation U P V)

/-- Restriction of a left-extension generator precomposes its actual chart arrow. -/
private def totalChartGeneratorRestriction (P : (SpacesEtale U)ᵒᵖ ⥤ Type u)
    {V W : sliceTotalSite U} (f : V ⟶ W) (s : TotalChartGenerator U P W) : TotalChartGenerator U P V :=
  ⟨s.1, (equivShrink _ (f ≫ (equivShrink _).symm s.2.1), s.2.2)⟩

/-- Restriction in the small coend is induced by precomposition on its generators. -/
private def totalChartExtensionRestriction (P : (SpacesEtale U)ᵒᵖ ⥤ Type u)
    {V W : sliceTotalSite U} (f : V ⟶ W) : totalChartExtensionValue U P W → totalChartExtensionValue U P V :=
  Quot.map (totalChartGeneratorRestriction U P f) (by
    rintro s t ⟨c, d, h, g, x, rfl, rfl⟩
    refine ⟨c, d, h, f ≫ g, x, ?_, ?_⟩
    · simp only [totalChartGeneratorRestriction, Equiv.symm_apply_apply]
    · simp only [totalChartGeneratorRestriction, Equiv.symm_apply_apply, Category.assoc])

/-- The coend extension is a presheaf; its laws follow from composition of actual chart arrows. -/
private def totalChartExtensionObj (P : (SpacesEtale U)ᵒᵖ ⥤ Type u) : (sliceTotalSite U)ᵒᵖ ⥤ Type u where
  obj V := totalChartExtensionValue U P V.unop
  map f := ↾(totalChartExtensionRestriction U P f.unop)
  map_id V := by
    ext x
    refine Quot.inductionOn x ?_
    intro s
    change Quot.mk _ (totalChartGeneratorRestriction U P (𝟙 V).unop s) = Quot.mk _ s
    congr 1
    cases s with
    | mk c s =>
      rcases s with ⟨g, x⟩
      simp only [totalChartGeneratorRestriction, unop_id, Category.id_comp, Equiv.apply_symm_apply]
  map_comp f g := by
    ext x
    refine Quot.inductionOn x ?_
    intro s
    change Quot.mk _ (totalChartGeneratorRestriction U P (g.unop ≫ f.unop) s) =
      Quot.mk _ (totalChartGeneratorRestriction U P g.unop (totalChartGeneratorRestriction U P f.unop s))
    congr 1
    rcases s with ⟨c, g, x⟩
    dsimp [totalChartGeneratorRestriction]
    simp only [Equiv.symm_apply_apply, Category.assoc]

/-- A map of presheaves acts on coend generators by its section maps. -/
private def totalChartGeneratorMap {P Q : (SpacesEtale U)ᵒᵖ ⥤ Type u} (α : P ⟶ Q)
    (V : sliceTotalSite U) (s : TotalChartGenerator U P V) : TotalChartGenerator U Q V :=
  ⟨s.1, s.2.1, α.app _ s.2.2⟩

/-- The coend map is the quotient of the componentwise map of generators. -/
private def totalChartExtensionMap {P Q : (SpacesEtale U)ᵒᵖ ⥤ Type u} (α : P ⟶ Q) :
    totalChartExtensionObj U P ⟶ totalChartExtensionObj U Q where
  app V := ↾(Quot.map (totalChartGeneratorMap U α V.unop) (by
    rintro s t ⟨c, d, h, f, x, rfl, rfl⟩
    refine ⟨c, d, h, f, α.app _ x, ?_, rfl⟩
    dsimp [totalChartGeneratorMap]
    congr 2
    exact ConcreteCategory.congr_hom (α.naturality
      ((totalChartInclusion U).map h).op) x))
  naturality {V W} f := by
    ext x
    refine Quot.inductionOn x ?_
    intro s
    rfl

/-- The small-chart coend extends presheaves from the étale site to the big slice. -/
private def totalChartExtension : ((SpacesEtale U)ᵒᵖ ⥤ Type u) ⥤ ((sliceTotalSite U)ᵒᵖ ⥤ Type u) where
  obj := totalChartExtensionObj U
  map := totalChartExtensionMap U
  map_id P := by
    ext V x
    refine Quot.inductionOn x ?_
    intro s
    rfl
  map_comp α β := by
    ext V x
    refine Quot.inductionOn x ?_
    intro s
    rfl

/-- Each chart section defines the coend generator with identity structural arrow. -/
private def totalChartUnit (P : (SpacesEtale U)ᵒᵖ ⥤ Type u) :
    (totalChartInclusion U).op ⋙ P ⟶
      (totalChartBigInclusion U).op ⋙ totalChartExtensionObj U P where
  app c := ↾fun x ↦ Quot.mk _ ⟨c.unop, equivShrink _ (𝟙 _), x⟩
  naturality {c d} h := by
    ext x
    apply Quot.sound
    refine ⟨d.unop, c.unop, h.unop, 𝟙 _, x, rfl, ?_⟩
    dsimp [totalChartExtensionObj, totalChartExtensionRestriction, totalChartGeneratorRestriction]
    simp only [Equiv.symm_apply_apply]
    change (⟨c.unop, equivShrink _ ((totalChartBigInclusion U).map h.unop ≫ 𝟙 _), x⟩ :
      TotalChartGenerator U P _) = ⟨c.unop, equivShrink _ (𝟙 _ ≫ (totalChartBigInclusion U).map h.unop), x⟩
    simp only [Category.comp_id, Category.id_comp]

/-- A map into a restricted presheaf evaluates each generator by its chart arrow. -/
private def totalChartHomInv {P : (SpacesEtale U)ᵒᵖ ⥤ Type u}
    {Q : (sliceTotalSite U)ᵒᵖ ⥤ Type u}
    (α : P ⟶ (toSliceTotal U).op ⋙ Q) :
    totalChartExtensionObj U P ⟶ Q where
  app V := ↾(Quot.lift (fun s : TotalChartGenerator U P V.unop ↦
    Q.map ((equivShrink _).symm s.2.1).op (α.app _ s.2.2)) (by
      rintro s t ⟨c, d, h, f, x, rfl, rfl⟩
      simp only [Equiv.symm_apply_apply, op_comp, CategoryTheory.Functor.map_comp]
      have e := ConcreteCategory.congr_hom
        (α.naturality ((totalChartInclusion U).map h).op) x
      exact congrArg (Q.map f.op) e))
  naturality {V W} f := by
    ext x
    refine Quot.inductionOn x ?_
    intro s
    change Q.map ((equivShrink _).symm
      (equivShrink _ (f.unop ≫ (equivShrink _).symm s.2.1))).op (α.app _ s.2.2) =
        Q.map f (Q.map ((equivShrink _).symm s.2.1).op (α.app _ s.2.2))
    rw [Equiv.symm_apply_apply, op_comp, Q.map_comp]
    rfl

/-- Restriction of a big fppf sheaf to étale objects is its comparison direct image. -/
def totalPushforward :
    Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u) ⥤ Sheaf (spacesEtaleTotalTopology U) (Type u) :=
  (toSliceTotal U).sheafPushforwardContinuous (Type u)
    (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)

/-- The comparison inverse image is the small-chart coend followed by twofold Plus. -/
def totalInverseImage :
    Sheaf (spacesEtaleTotalTopology U) (Type u) ⥤ Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u) :=
  sheafToPresheaf (spacesEtaleTotalTopology U) (Type u) ⋙ totalChartExtension U ⋙ totalFppfSheafification U

/-- The forward adjunction map restricts to charts and then extends uniquely through the dense family. -/
private def totalComparisonHomTo (P : Sheaf (spacesEtaleTotalTopology U) (Type u))
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (α : (totalInverseImage U).obj P ⟶ F) : P ⟶ (totalPushforward U).obj F :=
  ObjectProperty.homMk
    (Functor.IsCoverDense.restrictHomEquivHom
      (G := totalChartInclusion U)
      (ℱ' := (totalPushforward U).obj F)
      (totalChartUnit U P.obj ≫ Functor.whiskerLeft (totalChartBigInclusion U).op
        ((totalFppfSheafificationAdjunction U).homEquiv _ _ α)))

/-- The reverse adjunction map evaluates coend generators and amalgamates twice. -/
private def totalComparisonHomInv (P : Sheaf (spacesEtaleTotalTopology U) (Type u))
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (α : P ⟶ (totalPushforward U).obj F) : (totalInverseImage U).obj P ⟶ F :=
  ((totalFppfSheafificationAdjunction U).homEquiv _ _).symm (totalChartHomInv U α.hom)

/-- Chart evaluation and twofold amalgamation are inverse natural hom correspondences. -/
theorem totalComparison_adjunction_laws :
    (∀ (P : Sheaf (spacesEtaleTotalTopology U) (Type u))
      (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)),
      (∀ α, totalComparisonHomInv U P F (totalComparisonHomTo U P F α) = α) ∧
      (∀ α, totalComparisonHomTo U P F (totalComparisonHomInv U P F α) = α)) ∧
    (∀ {P Q : Sheaf (spacesEtaleTotalTopology U) (Type u)} (α : P ⟶ Q)
      {F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)} (β : Q ⟶ (totalPushforward U).obj F),
      totalComparisonHomInv U P F (α ≫ β) =
        (totalInverseImage U).map α ≫ totalComparisonHomInv U Q F β) ∧
    (∀ {P : Sheaf (spacesEtaleTotalTopology U) (Type u)}
      {F G : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)}
      (α : (totalInverseImage U).obj P ⟶ F) (β : F ⟶ G),
      totalComparisonHomTo U P G (α ≫ β) =
        totalComparisonHomTo U P F α ≫ (totalPushforward U).map β) := by
  sorry

/-- The small-chart comparison inverse image preserves finite limits. -/
theorem totalComparison_preservesFiniteLimits :
    PreservesFiniteLimits (totalInverseImage U) := by
  sorry

/-- The fppf-to-étale comparison is defined with small coefficients and explicit chartwise inverse image. -/
def fppfEtaleComparison :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) where
  inverseImageFunctor := ⟨totalInverseImage U, totalComparison_preservesFiniteLimits U⟩
  pushforward := totalPushforward U
  adjunction := Adjunction.mkOfHomEquiv
    { homEquiv := fun P F ↦
        { toFun := totalComparisonHomTo U P F
          invFun := totalComparisonHomInv U P F
          left_inv := ((totalComparison_adjunction_laws U).1 P F).1
          right_inv := ((totalComparison_adjunction_laws U).1 P F).2 }
      homEquiv_naturality_left_symm := fun f g ↦ (totalComparison_adjunction_laws U).2.1 f g
      homEquiv_naturality_right := fun f g ↦ (totalComparison_adjunction_laws U).2.2 f g }

/-- Composition of small-coefficient étale inverse images is the mate of the canonical pullback comparison. -/
private def smallStageComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesRingedMorphismOfTopoi (f ≫ g)).inverseImage ≅
      (spacesRingedMorphismOfTopoi g).inverseImage ⋙ (spacesRingedMorphismOfTopoi f).inverseImage :=
  Adjunction.leftAdjointUniq (spacesRingedMorphismOfTopoi (f ≫ g)).adjunction
    (((spacesRingedMorphismOfTopoi g).adjunction.comp
      (spacesRingedMorphismOfTopoi f).adjunction).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp' (spacesEtalePullbackComp f g).symm
        (Type u) (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X)))

/-- The étale topos morphism associated to a simplex operator. -/
private abbrev etaleStageMap {m n : SimplexCategory} (φ : m ⟶ n) :=
  spacesRingedMorphismOfTopoi (U.map φ.op)

/-- Pullback along the identity simplex is canonically the identity site functor. -/
private def etaleStageId (n : SimplexCategory) :
    spacesEtalePullback (U.map (𝟙 n).op) ≅ 𝟭 (spacesEtaleSite (U.obj (op n))) :=
  let e : MorphismProperty.Over.map (P := @Etale S) ⊤
      (f := 𝟙 (U.obj (op n))) inferInstance ≅ 𝟭 (spacesEtaleSite (U.obj (op n))) :=
    NatIso.ofComponents
      (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _)
        (by change 𝟙 V.left ≫ V.hom = V.hom ≫ 𝟙 _; simp))
      (by intro V W f; ext; change f.left ≫ 𝟙 W.left = 𝟙 V.left ≫ f.left; simp)
  MorphismProperty.Over.pullbackCongr (by simpa using U.map_id (op n)) ≪≫
    ((MorphismProperty.Over.mapPullbackAdj (@Etale S) ⊤ (𝟙 (U.obj (op n)))
      inferInstance trivial).ofNatIsoLeft e).rightAdjointUniq Adjunction.id

/-- Composition of simplex operators induces the canonical base-change comparison. -/
private def etaleStageComp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    spacesEtalePullback (U.map ψ.op) ⋙ spacesEtalePullback (U.map φ.op) ≅
      spacesEtalePullback (U.map (ψ ≫ φ).op) :=
  (spacesEtalePullbackComp (U.map φ.op) (U.map ψ.op)).symm ≪≫
    MorphismProperty.Over.pullbackCongr (by simpa using (U.map_comp φ.op ψ.op).symm)

/-- Stage direct images have their canonical identity and composition comparisons. -/
private instance etaleStageFunctoriality :
    HasPushforwardFunctoriality
      (fun n : SimplexCategory ↦ spacesEtaleTopology (U.obj (op n)))
      (fun φ ↦ etaleStageMap U φ) where
  pushforwardIdIso n :=
    Functor.sheafPushforwardContinuousId' (etaleStageId U n) (Type u)
      (spacesEtaleTopology (U.obj (op n)))
  pushforwardCompIso ψ φ :=
    Functor.sheafPushforwardContinuousComp' (etaleStageComp U ψ φ) (Type u)
      (spacesEtaleTopology (U.obj (op _)))
      (spacesEtaleTopology (U.obj (op _)))
      (spacesEtaleTopology (U.obj (op _)))

/-- Systems of stage étale sheaves with transitions along the simplicial structure maps. -/
private abbrev EtaleSystem :=
  SheafSystem (fun n : SimplexCategory ↦ spacesEtaleTopology (U.obj (op n)))
    (fun φ ↦ etaleStageMap U φ)

/-- Restriction of a total presheaf to a stage. -/
private def etaleRestrictionPresheaf (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    (n : SimplexCategory) := (SpacesEtale.includeStage (U := U) (op n)).op ⋙ F.obj

/-- Stage restrictions of total sheaves satisfy the sheaf condition. -/
private abbrev etaleRestrictionSheafLaw :=
  ∀ (F : Sheaf (spacesEtaleTotalTopology U) (Type u)) (n : SimplexCategory),
    Presheaf.IsSheaf (spacesEtaleTopology (U.obj (op n))) (etaleRestrictionPresheaf U F n)

/-- Restriction to a stage, with its sheaf-condition proof displayed. -/
private def etaleRestriction (h : etaleRestrictionSheafLaw U) (n : SimplexCategory) :
    Sheaf (spacesEtaleTotalTopology U) (Type u) ⥤
      Sheaf (spacesEtaleTopology (U.obj (op n))) (Type u) where
  obj F := ⟨etaleRestrictionPresheaf U F n, h F n⟩
  map α := ObjectProperty.homMk
    { app := fun V ↦ α.hom.app ((SpacesEtale.includeStage (U := U) (op n)).op.obj V)
      naturality := by intro V W f; exact α.hom.naturality _ }
  map_id := by intro F; ext V x; rfl
  map_comp := by intro F G H α β; ext V x; rfl

/-- Transition on sections is restriction along the canonical cartesian square. -/
private def toEtaleTransitionApp (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) (V : (spacesEtaleSite (U.obj (op m)))ᵒᵖ) :=
  F.obj.map (SpacesEtale.homEquivFromPullback
    (Y := (SpacesEtale.ofStage (op n) ((spacesEtalePullback (U.map φ.op)).obj V.unop) : SpacesEtale U))
    (Z := (SpacesEtale.ofStage (op m) V.unop : SpacesEtale U)) φ (𝟙 _)).op

/-- Section transitions commute with restrictions within a stage. -/
private abbrev toEtaleTransitionLaw :=
  ∀ (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n)
    {V W : (spacesEtaleSite (U.obj (op m)))ᵒᵖ} (η : V ⟶ W),
    (etaleRestrictionPresheaf U F m).map η ≫ toEtaleTransitionApp U F φ W =
      toEtaleTransitionApp U F φ V ≫
        (etaleRestrictionPresheaf U F n).map ((spacesEtalePullback (U.map φ.op)).op.map η)

/-- Stage transitions as maps to direct images. -/
private def toEtaleTransition (hs : etaleRestrictionSheafLaw U)
    (hn : toEtaleTransitionLaw U)
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (etaleRestriction U hs m).obj F ⟶
      (etaleStageMap U φ).pushforward.obj ((etaleRestriction U hs n).obj F) :=
  ObjectProperty.homMk
    { app := toEtaleTransitionApp U F φ
      naturality := fun _ _ η ↦ hn F φ η }

/-- Restriction and cartesian-square transitions define a functor to stage sheaf systems. -/
theorem etaleStageFunctoriality_laws :
    etaleRestrictionSheafLaw U ∧ toEtaleTransitionLaw U ∧
    ∀ (hs : etaleRestrictionSheafLaw U) (hn : toEtaleTransitionLaw U),
    (∀ (F : Sheaf (spacesEtaleTotalTopology U) (Type u)) (n : SimplexCategory),
      toEtaleTransition U hs hn F (𝟙 n) =
        (HasPushforwardFunctoriality.pushforwardIdIso (fHom := fun φ ↦ etaleStageMap U φ) n).inv.app
          ((etaleRestriction U hs n).obj F)) ∧
    (∀ (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
      {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      toEtaleTransition U hs hn F (ψ ≫ φ) =
        toEtaleTransition U hs hn F ψ ≫ (etaleStageMap U ψ).pushforward.map
          (toEtaleTransition U hs hn F φ) ≫
        (HasPushforwardFunctoriality.pushforwardCompIso (fHom := fun φ ↦ etaleStageMap U φ) ψ φ).hom.app
          ((etaleRestriction U hs n).obj F)) ∧
    (∀ {F G : Sheaf (spacesEtaleTotalTopology U) (Type u)} (α : F ⟶ G)
      {m n : SimplexCategory} (φ : m ⟶ n),
      toEtaleTransition U hs hn F φ ≫ (etaleStageMap U φ).pushforward.map
        ((etaleRestriction U hs n).map α) =
      (etaleRestriction U hs m).map α ≫ toEtaleTransition U hs hn G φ) :=
  sorry

/-- The sheaf system obtained by restricting a total étale sheaf to every stage. -/
def toEtaleSheafSystem :
    Sheaf (spacesEtaleTotalTopology U) (Type u) ⥤ EtaleSystem U where
  obj F := SheafSystem.of
    (fun n ↦ (etaleRestriction U (etaleStageFunctoriality_laws U).1 n).obj F)
    (fun φ ↦ toEtaleTransition U (etaleStageFunctoriality_laws U).1 (etaleStageFunctoriality_laws U).2.1 F φ)
    (((etaleStageFunctoriality_laws U).2.2 _ _).1 F)
    (((etaleStageFunctoriality_laws U).2.2 _ _).2.1 F)
  map α := SheafSystem.homMk
    (fun n ↦ (etaleRestriction U (etaleStageFunctoriality_laws U).1 n).map α)
    (((etaleStageFunctoriality_laws U).2.2 _ _).2.2 α)
  map_id := by intro F; apply SheafSystem.Hom.ext; intro n; ext V x; rfl
  map_comp := by intro F G H α β; apply SheafSystem.Hom.ext; intro n; ext V x; rfl

/-- Restriction on sections associated to a commutative-square morphism. -/
private def fromEtaleMap (F : EtaleSystem U) {Y Z : SpacesEtale U} (f : Y ⟶ Z) :=
  (F.map f.simplex).hom.app (op Z.obj) ≫
    (F.obj Y.index.unop).obj.map (SpacesEtale.homEquivToPullback f).op

/-- Assembly on sections respects identities and composition. -/
private abbrev fromEtaleFunctorLaw :=
  ∀ F : EtaleSystem U,
    (∀ Y : SpacesEtale U, fromEtaleMap U F (𝟙 Y) = 𝟙 _) ∧
    (∀ {Y Z W : SpacesEtale U} (f : Y ⟶ Z) (g : Z ⟶ W),
      fromEtaleMap U F (f ≫ g) = fromEtaleMap U F g ≫ fromEtaleMap U F f)

/-- The presheaf assembled by evaluation of the stage sheaves. -/
private def fromEtalePresheaf (h : fromEtaleFunctorLaw U) (F : EtaleSystem U) :
    (SpacesEtale U)ᵒᵖ ⥤ Type u where
  obj Y := (F.obj Y.unop.index.unop).obj.obj (op Y.unop.obj)
  map f := fromEtaleMap U F f.unop
  map_id Y := (h F).1 Y.unop
  map_comp f g := (h F).2 g.unop f.unop

/-- Stagewise assembly is a sheaf and carries system maps to natural section maps. -/
theorem etaleSheafSystem_laws :
    fromEtaleFunctorLaw U ∧
    (∀ (h : fromEtaleFunctorLaw U) (F : EtaleSystem U),
      Presheaf.IsSheaf (spacesEtaleTotalTopology U) (fromEtalePresheaf U h F)) ∧
    (∀ {F G : EtaleSystem U} (α : F ⟶ G)
      {Y Z : SpacesEtale U} (f : Y ⟶ Z),
      fromEtaleMap U F f ≫ (α.app Y.index.unop).hom.app (op Y.obj) =
        (α.app Z.index.unop).hom.app (op Z.obj) ≫ fromEtaleMap U G f) :=
  sorry

/-- Assemble a total étale sheaf from its stage sheaves and transition maps. -/
def fromEtaleSheafSystem :
    EtaleSystem U ⥤ Sheaf (spacesEtaleTotalTopology U) (Type u) where
  obj F := ⟨fromEtalePresheaf U (etaleSheafSystem_laws U).1 F,
    (etaleSheafSystem_laws U).2.1 _ F⟩
  map α := ObjectProperty.homMk
    { app := fun Y ↦ (α.app Y.unop.index.unop).hom.app (op Y.unop.obj)
      naturality := fun _ _ f ↦ (etaleSheafSystem_laws U).2.2 α f.unop }
  map_id := by intro F; ext Y x; rfl
  map_comp := by intro F G H α β; ext Y x; rfl

/-- Restriction followed by assembly has identity section maps in both directions. -/
private abbrev EtaleUnitLaw : Prop :=
  ∀ (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    {Y Z : (SpacesEtale U)ᵒᵖ} (f : Y ⟶ Z),
    (F.obj.map f ≫ 𝟙 _ = 𝟙 _ ≫
      ((toEtaleSheafSystem U ⋙ fromEtaleSheafSystem U).obj F).obj.map f) ∧
    (((toEtaleSheafSystem U ⋙ fromEtaleSheafSystem U).obj F).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ F.obj.map f)

/-- The identity section comparison from a total sheaf to its restriction and assembly. -/
private def etaleSheafSystemUnit (hu : EtaleUnitLaw U) :
    𝟭 (Sheaf (spacesEtaleTotalTopology U) (Type u)) ≅
      toEtaleSheafSystem U ⋙ fromEtaleSheafSystem U :=
  NatIso.ofComponents (fun F ↦
    { hom := ObjectProperty.homMk
        { app := fun _ ↦ 𝟙 _
          naturality := fun _ _ f ↦ (hu F f).1 }
      inv := ObjectProperty.homMk
        { app := fun _ ↦ 𝟙 _
          naturality := fun _ _ f ↦ (hu F f).2 }
      hom_inv_id := by ext Y x; rfl
      inv_hom_id := by ext Y x; rfl })
    (by intro F G α; ext Y x; rfl)

/-- Assembly followed by restriction has identity section maps on each stage. -/
private abbrev EtaleCounitLaw : Prop :=
  ∀ (F : EtaleSystem U) (n : SimplexCategory)
    {V W : (spacesEtaleSite (U.obj (op n)))ᵒᵖ} (f : V ⟶ W),
    ((((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).obj n).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (F.obj n).obj.map f) ∧
    ((F.obj n).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).obj n).obj.map f)

/-- The identity stage comparison from restriction of assembly to the original system. -/
private def etaleCounitApp (hc : EtaleCounitLaw U) (F : EtaleSystem U) (n : SimplexCategory) :
    ((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).obj n ⟶ F.obj n :=
  ObjectProperty.homMk
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ f ↦ (hc F n f).1 }

/-- The inverse identity comparison on stage sections. -/
private def etaleCounitInvApp (hc : EtaleCounitLaw U) (F : EtaleSystem U) (n : SimplexCategory) :
    F.obj n ⟶ ((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).obj n :=
  ObjectProperty.homMk
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ f ↦ (hc F n f).2 }

/-- The identity stage comparisons commute with all system transitions. -/
theorem etaleSheafSystem_equivalence_laws :
    EtaleUnitLaw U ∧ EtaleCounitLaw U ∧
    ∀ (hc : EtaleCounitLaw U) (F : EtaleSystem U)
    {m n : SimplexCategory} (φ : m ⟶ n),
    (((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).map φ ≫
      (etaleStageMap U φ).pushforward.map (etaleCounitApp U hc F n) =
      etaleCounitApp U hc F m ≫ F.map φ) ∧
    (F.map φ ≫ (etaleStageMap U φ).pushforward.map (etaleCounitInvApp U hc F n) =
      etaleCounitInvApp U hc F m ≫
        ((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).map φ) := by
  sorry

/-- The canonical stagewise identity counit of restriction and assembly. -/
private def etaleSheafSystemCounit :
    fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U ≅ 𝟭 (EtaleSystem U) :=
  NatIso.ofComponents (fun F ↦
    { hom := SheafSystem.homMk (etaleCounitApp U (etaleSheafSystem_equivalence_laws U).2.1 F)
        (fun φ ↦ ((etaleSheafSystem_equivalence_laws U).2.2 (etaleSheafSystem_equivalence_laws U).2.1 F φ).1)
      inv := SheafSystem.homMk (etaleCounitInvApp U (etaleSheafSystem_equivalence_laws U).2.1 F)
        (fun φ ↦ ((etaleSheafSystem_equivalence_laws U).2.2 (etaleSheafSystem_equivalence_laws U).2.1 F φ).2)
      hom_inv_id := by apply SheafSystem.Hom.ext; intro n; ext V x; rfl
      inv_hom_id := by apply SheafSystem.Hom.ext; intro n; ext V x; rfl })
    (by intro F G α; apply SheafSystem.Hom.ext; intro n; ext V x; rfl)

/-- Total étale sheaves are equivalent to their systems of stage sheaves. -/
def etaleSheafSystemEquivalence :
    Sheaf (spacesEtaleTotalTopology U) (Type u) ≌ EtaleSystem U :=
  CategoryTheory.Equivalence.mk (toEtaleSheafSystem U) (fromEtaleSheafSystem U)
    (etaleSheafSystemUnit U (etaleSheafSystem_equivalence_laws U).1) (etaleSheafSystemCounit U)

variable {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- The canonical inverse-image comparison supplied by augmentation naturality. -/
private def etaleAugmentationStageComp {m n : SimplexCategory} (φ : m ⟶ n) :
    (spacesRingedMorphismOfTopoi (a.app (op m)))⁻¹ ⋙ (etaleStageMap U φ)⁻¹ ≅
      (spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹ :=
  (smallStageComp (U.map φ.op) (a.app (op m))).symm ≪≫
    eqToIso (congrArg (fun f ↦ (spacesRingedMorphismOfTopoi f).inverseImage)
      ((a.naturality φ.op).trans (Category.comp_id _)))

/-- The augmentation inverse-image transition is the mate of the stage comparison. -/
private def etaleAugmentationTransition
    (G : Sheaf (spacesEtaleTopology X) (Type u))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (spacesRingedMorphismOfTopoi (a.app (op m)))⁻¹.obj G ⟶
      (etaleStageMap U φ).pushforward.obj
        ((spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.obj G) :=
  (etaleStageMap U φ).adjunction.homEquiv _ _
    ((etaleAugmentationStageComp U a φ).hom.app G)

/-- The augmentation stage inverse images and their canonical transitions are functorial. -/
theorem etaleAugmentation_inverseImage_laws :
    (∀ (G : Sheaf (spacesEtaleTopology X) (Type u)) (n : SimplexCategory),
      etaleAugmentationTransition U a G (𝟙 n) =
        (HasPushforwardFunctoriality.pushforwardIdIso (fHom := fun φ ↦ etaleStageMap U φ) n).inv.app
          ((spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.obj G)) ∧
    (∀ (G : Sheaf (spacesEtaleTopology X) (Type u))
      {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      etaleAugmentationTransition U a G (ψ ≫ φ) =
        etaleAugmentationTransition U a G ψ ≫ (etaleStageMap U ψ).pushforward.map
          (etaleAugmentationTransition U a G φ) ≫
        (HasPushforwardFunctoriality.pushforwardCompIso (fHom := fun φ ↦ etaleStageMap U φ) ψ φ).hom.app
          ((spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.obj G)) ∧
    (∀ {G H : Sheaf (spacesEtaleTopology X) (Type u)} (α : G ⟶ H)
      {m n : SimplexCategory} (φ : m ⟶ n),
      etaleAugmentationTransition U a G φ ≫ (etaleStageMap U φ).pushforward.map
        ((spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.map α) =
      (spacesRingedMorphismOfTopoi (a.app (op m)))⁻¹.map α ≫ etaleAugmentationTransition U a H φ) :=
  sorry

/-- The system of all stage inverse images along an augmentation. -/
private def etaleAugmentationInverseSystem :
    Sheaf (spacesEtaleTopology X) (Type u) ⥤ EtaleSystem U where
  obj G := SheafSystem.of
    (fun n ↦ (spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.obj G)
    (fun φ ↦ etaleAugmentationTransition U a G φ)
    ((etaleAugmentation_inverseImage_laws U a).1 G)
    ((etaleAugmentation_inverseImage_laws U a).2.1 G)
  map α := SheafSystem.homMk
    (fun n ↦ (spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.map α)
    ((etaleAugmentation_inverseImage_laws U a).2.2 α)
  map_id := by
    intro G; apply SheafSystem.Hom.ext; intro n
    exact (spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.map_id G
  map_comp := by
    intro G H K α β; apply SheafSystem.Hom.ext; intro n
    exact (spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.map_comp α β

/-- Total inverse image assembled from all stage inverse images. -/
private def etaleAugmentationInverseImage :=
  etaleAugmentationInverseSystem U a ⋙ fromEtaleSheafSystem U

/-- Direct-image comparison corresponding to augmentation naturality. -/
private def etaleAugmentationStagePushforward {m n : SimplexCategory} (φ : m ⟶ n) :
    (etaleStageMap U φ).pushforward ⋙ (spacesRingedMorphismOfTopoi (a.app (op m))).pushforward ≅
      (spacesRingedMorphismOfTopoi (a.app (op n))).pushforward :=
  MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
    ((spacesRingedMorphismOfTopoi (a.app (op m))).comp (etaleStageMap U φ))
    (spacesRingedMorphismOfTopoi (a.app (op n))) (etaleAugmentationStageComp U a φ)

/-- The two coface maps between degree-zero and degree-one stage direct images. -/
def spacesEtaleAugmentationParallel
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u)) (i : Fin 2) :
    (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.obj
      (((toEtaleSheafSystem U).obj F).obj ⦋0⦌) ⟶
    (spacesRingedMorphismOfTopoi (a.app (op ⦋1⦌))).pushforward.obj
      (((toEtaleSheafSystem U).obj F).obj ⦋1⦌) :=
  (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
    (((toEtaleSheafSystem U).obj F).map (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)) ≫
  (etaleAugmentationStagePushforward U a (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).hom.app
    (((toEtaleSheafSystem U).obj F).obj ⦋1⦌)

/-- Maps of total sheaves induce maps between the coface equalizers. -/
theorem etaleAugmentation_pushforward_laws
    {F G : Sheaf (spacesEtaleTotalTopology U) (Type u)} (α : F ⟶ G) :
    (equalizer.ι (spacesEtaleAugmentationParallel U a F 0) (spacesEtaleAugmentationParallel U a F 1) ≫
      (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
        (((toEtaleSheafSystem U).map α).app ⦋0⦌)) ≫ spacesEtaleAugmentationParallel U a G 0 =
    (equalizer.ι (spacesEtaleAugmentationParallel U a F 0) (spacesEtaleAugmentationParallel U a F 1) ≫
      (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
        (((toEtaleSheafSystem U).map α).app ⦋0⦌)) ≫ spacesEtaleAugmentationParallel U a G 1 :=
  sorry

/-- Direct image is the equalizer of the two coface maps on stage direct images. -/
private def etaleAugmentationPushforward :
    Sheaf (spacesEtaleTotalTopology U) (Type u) ⥤
      Sheaf (spacesEtaleTopology X) (Type u) where
  obj F := equalizer (spacesEtaleAugmentationParallel U a F 0) (spacesEtaleAugmentationParallel U a F 1)
  map α := equalizer.lift
    (equalizer.ι (spacesEtaleAugmentationParallel U a _ 0) (spacesEtaleAugmentationParallel U a _ 1) ≫
      (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
        (((toEtaleSheafSystem U).map α).app ⦋0⦌))
    (etaleAugmentation_pushforward_laws U a α)
  map_id := by
    intro F
    apply equalizer.hom_ext
    simp only [equalizer.lift_ι, CategoryTheory.Functor.map_id]
    change _ ≫ (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map (𝟙 _) = _
    simp
    rfl
  map_comp := by
    intro F G H α β
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι]
    change _ ≫ (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
      (((toEtaleSheafSystem U).map (α ≫ β)).app ⦋0⦌) = _
    rw [(toEtaleSheafSystem U).map_comp]
    change _ ≫ (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
      ((((toEtaleSheafSystem U).map α).app ⦋0⦌) ≫
        (((toEtaleSheafSystem U).map β).app ⦋0⦌)) = _
    rw [CategoryTheory.Functor.map_comp]
    simp only [← Category.assoc, equalizer.lift_ι]
    congr 1
    exact (equalizer.lift_ι _ _).symm

/-- The degree-zero adjoint of a total sheaf map. -/
private def etaleAugmentationHomToZero
    (G : Sheaf (spacesEtaleTopology X) (Type u))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    (α : (etaleAugmentationInverseImage U a).obj G ⟶ F) :=
  (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).adjunction.homEquiv G
    (((toEtaleSheafSystem U).obj F).obj ⦋0⦌)
    (((etaleSheafSystemCounit U).inv.app ((etaleAugmentationInverseSystem U a).obj G) ≫
      (toEtaleSheafSystem U).map α).app ⦋0⦌)

/-- The degree-zero adjoint coequalizes the two coface maps. -/
private abbrev etaleAugmentationHomToLaw :=
  ∀ (G : Sheaf (spacesEtaleTopology X) (Type u))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    (α : (etaleAugmentationInverseImage U a).obj G ⟶ F),
    etaleAugmentationHomToZero U a G F α ≫ spacesEtaleAugmentationParallel U a F 0 =
      etaleAugmentationHomToZero U a G F α ≫ spacesEtaleAugmentationParallel U a F 1

/-- The forward adjunction map factors the degree-zero adjoint through the equalizer. -/
private def etaleAugmentationHomTo (h : etaleAugmentationHomToLaw U a)
    (G : Sheaf (spacesEtaleTopology X) (Type u))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    (α : (etaleAugmentationInverseImage U a).obj G ⟶ F) :
    G ⟶ (etaleAugmentationPushforward U a).obj F :=
  equalizer.lift (etaleAugmentationHomToZero U a G F α) (h G F α)

/-- The stage component reconstructed from a map to the equalizer. -/
private def etaleAugmentationHomInvApp
    (G : Sheaf (spacesEtaleTopology X) (Type u))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    (β : G ⟶ (etaleAugmentationPushforward U a).obj F) (n : SimplexCategory) :
    (spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.obj G ⟶
      ((toEtaleSheafSystem U).obj F).obj n :=
  (etaleAugmentationStageComp U a (SimplexCategory.const ⦋0⦌ n 0)).inv.app G ≫
    (etaleStageMap U (SimplexCategory.const ⦋0⦌ n 0)).inverseImage.map
      (((spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).adjunction.homEquiv G
        (((toEtaleSheafSystem U).obj F).obj ⦋0⦌)).symm
        (β ≫ equalizer.ι (spacesEtaleAugmentationParallel U a F 0) (spacesEtaleAugmentationParallel U a F 1))) ≫
    SheafSystem.mapInverseImage ((toEtaleSheafSystem U).obj F) (SimplexCategory.const ⦋0⦌ n 0)

/-- The reconstructed stage components commute with simplex transitions. -/
private abbrev etaleAugmentationHomInvLaw :=
  ∀ (G : Sheaf (spacesEtaleTopology X) (Type u))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    (β : G ⟶ (etaleAugmentationPushforward U a).obj F)
    {m n : SimplexCategory} (φ : m ⟶ n),
    ((etaleAugmentationInverseSystem U a).obj G).map φ ≫
      (etaleStageMap U φ).pushforward.map (etaleAugmentationHomInvApp U a G F β n) =
      etaleAugmentationHomInvApp U a G F β m ≫ ((toEtaleSheafSystem U).obj F).map φ

/-- The inverse adjunction map assembles the reconstructed stage maps. -/
private def etaleAugmentationHomInv (h : etaleAugmentationHomInvLaw U a)
    (G : Sheaf (spacesEtaleTopology X) (Type u))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u))
    (β : G ⟶ (etaleAugmentationPushforward U a).obj F) :
    (etaleAugmentationInverseImage U a).obj G ⟶ F :=
  (fromEtaleSheafSystem U).map
    (SheafSystem.homMk (etaleAugmentationHomInvApp U a G F β) (h G F β)) ≫
    (etaleSheafSystemUnit U (etaleSheafSystem_equivalence_laws U).1).inv.app F

/-- The equalizer adjunction maps are defined and inverse to each other. -/
theorem etaleAugmentation_adjunction_laws :
    (etaleAugmentationHomToLaw U a ∧ etaleAugmentationHomInvLaw U a ∧
    ∀ (ht : etaleAugmentationHomToLaw U a) (hi : etaleAugmentationHomInvLaw U a)
      (G : Sheaf (spacesEtaleTopology X) (Type u))
      (F : Sheaf (spacesEtaleTotalTopology U) (Type u)),
    Function.LeftInverse (etaleAugmentationHomInv U a hi G F) (etaleAugmentationHomTo U a ht G F) ∧
    Function.RightInverse (etaleAugmentationHomInv U a hi G F) (etaleAugmentationHomTo U a ht G F)) ∧
    ∀ (ht : etaleAugmentationHomToLaw U a) (hi : etaleAugmentationHomInvLaw U a),
    (∀ {G' G : Sheaf (spacesEtaleTopology X) (Type u)}
      {F : Sheaf (spacesEtaleTotalTopology U) (Type u)}
      (f : G' ⟶ G) (g : G ⟶ (etaleAugmentationPushforward U a).obj F),
      (etaleAugmentationHomInv U a hi G' F) (f ≫ g) =
        (etaleAugmentationInverseImage U a).map f ≫ (etaleAugmentationHomInv U a hi G F) g) ∧
    (∀ {G : Sheaf (spacesEtaleTopology X) (Type u)}
      {F F' : Sheaf (spacesEtaleTotalTopology U) (Type u)}
      (f : (etaleAugmentationInverseImage U a).obj G ⟶ F) (g : F ⟶ F'),
      (etaleAugmentationHomTo U a ht G F') (f ≫ g) =
        (etaleAugmentationHomTo U a ht G F) f ≫ (etaleAugmentationPushforward U a).map g) := by
  sorry

/-- The Hom-set equivalence of the total étale augmentation adjunction. -/
private def etaleAugmentationHomEquiv
    (G : Sheaf (spacesEtaleTopology X) (Type u))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u)) :
    ((etaleAugmentationInverseImage U a).obj G ⟶ F) ≃
      (G ⟶ (etaleAugmentationPushforward U a).obj F) where
  toFun := etaleAugmentationHomTo U a ((etaleAugmentation_adjunction_laws U a).1).1 G F
  invFun := etaleAugmentationHomInv U a ((etaleAugmentation_adjunction_laws U a).1).2.1 G F
  left_inv := (((etaleAugmentation_adjunction_laws U a).1).2.2 _ _ G F).1
  right_inv := (((etaleAugmentation_adjunction_laws U a).1).2.2 _ _ G F).2

/-- The assembled augmentation inverse image preserves finite limits. -/
theorem etaleAugmentation_inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (etaleAugmentationInverseImage U a) :=
  sorry

/-- The total étale augmentation has stagewise inverse image and equalizer direct image. -/
def spacesEtaleAugmentation :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u} (spacesEtaleTopology X) (spacesEtaleTotalTopology U) where
  inverseImageFunctor := ⟨etaleAugmentationInverseImage U a,
    etaleAugmentation_inverseImage_preservesFiniteLimits U a⟩
  pushforward := etaleAugmentationPushforward U a
  adjunction := Adjunction.mkOfHomEquiv
    { homEquiv := etaleAugmentationHomEquiv U a
      homEquiv_naturality_left_symm := ((etaleAugmentation_adjunction_laws U a).2
        (etaleAugmentation_adjunction_laws U a).1.1
        (etaleAugmentation_adjunction_laws U a).1.2.1).1
      homEquiv_naturality_right := ((etaleAugmentation_adjunction_laws U a).2
        (etaleAugmentation_adjunction_laws U a).1.1
        (etaleAugmentation_adjunction_laws U a).1.2.1).2 }

/-- Sections of total augmentation inverse image are the corresponding stage inverse-image sections. -/
theorem spacesEtaleAugmentation_inverseImage_obj
    (G : Sheaf (spacesEtaleTopology X) (Type u)) (Y : SpacesEtale U) :
    ((spacesEtaleAugmentation U a)⁻¹.obj G).obj.obj (op Y) =
      ((spacesRingedMorphismOfTopoi (a.app Y.index))⁻¹.obj G).obj.obj (op Y.obj) := rfl

/-- Total augmentation direct image is the equalizer of the two coface maps on stage direct images. -/
theorem spacesEtaleAugmentation_pushforward_obj
    (F : Sheaf (spacesEtaleTotalTopology U) (Type u)) :
    (spacesEtaleAugmentation U a).pushforward.obj F =
      equalizer (spacesEtaleAugmentationParallel U a F 0)
        (spacesEtaleAugmentationParallel U a F 1) := rfl

/-- Restriction of a total étale sheaf to a specified stage. -/
def spacesEtaleRestrict (n : SimplexCategory) :=
  etaleRestriction U (etaleStageFunctoriality_laws U).1 n

/-- Restricting the augmentation inverse image has the same sections as stage inverse image. -/
private theorem spacesEtaleAugmentation_restrict_naturality
    (G : Sheaf (spacesEtaleTopology X) (Type u)) (n : SimplexCategory)
    {V W : (spacesEtaleSite (U.obj (op n)))ᵒᵖ} (f : V ⟶ W) :
    ((((spacesEtaleAugmentation U a)⁻¹ ⋙ spacesEtaleRestrict U n).obj G).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ ((spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.obj G).obj.map f) ∧
    (((spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹.obj G).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (((spacesEtaleAugmentation U a)⁻¹ ⋙ spacesEtaleRestrict U n).obj G).obj.map f) := by
  exact (etaleSheafSystem_equivalence_laws U).2.1
    ((etaleAugmentationInverseSystem U a).obj G) n f

/-- In every simplicial degree, total augmentation inverse image restricts to the actual stage inverse image. -/
def spacesEtaleAugmentation_restrict (n : SimplexCategory) :
    (spacesEtaleAugmentation U a)⁻¹ ⋙ spacesEtaleRestrict U n ≅
      (spacesRingedMorphismOfTopoi (a.app (op n)))⁻¹ :=
  NatIso.ofComponents (fun G ↦
    { hom := ObjectProperty.homMk
        { app := fun _ ↦ 𝟙 _
          naturality := fun _ _ f ↦ (spacesEtaleAugmentation_restrict_naturality U a G n f).1 }
      inv := ObjectProperty.homMk
        { app := fun _ ↦ 𝟙 _
          naturality := fun _ _ f ↦ (spacesEtaleAugmentation_restrict_naturality U a G n f).2 }
      hom_inv_id := by ext V x; rfl
      inv_hom_id := by ext V x; rfl })
    (by intro G H α; ext V x; rfl)


/-- Pullback to a specified degree, included in the total slice category. -/
def fppfAugmentationStage (n : SimplexCategory) : Over X ⥤ sliceTotalSite U :=
  Over.pullback (a.app (op n)) ⋙ Grothendieck.ι (sliceDiagram U) (op n)

/-- Pullback to a stage is continuous for the fppf slice and total topologies. -/
instance fppfAugmentationStage_continuous (n : SimplexCategory) :
    (fppfAugmentationStage U a n).IsContinuous (overFppfTopology X)
      (sliceTotalTopology (fppfTopology S) U) := by
  have hι := Grothendieck.HasSheafTransitions.component_continuous
    (F := sliceDiagram U) (J := slicePrecoverage (fppfTopology S) U) n
  rw [show (slicePrecoverage (fppfTopology S) U (op n)).toGrothendieck =
    (fppfTopology S).over (U.obj (op n)) from by
      change ((fppfTopology S).over (U.obj (op n))).toPrecoverage.toGrothendieck = _
      apply le_antisymm (GrothendieckTopology.toGrothendieck_toPrecoverage_le _)
      intro V R hR
      have h : R.arrows ∈ ((fppfTopology S).over (U.obj (op n))).toPrecoverage V := by
        change Sieve.generate R.arrows ∈ (fppfTopology S).over (U.obj (op n)) V
        simpa using hR
      simpa using (Precoverage.generate_mem_toGrothendieck h)] at hι
  exact @Functor.isContinuous_comp _ _ _ _ _ _
    (Over.pullback (a.app (op n))) (Grothendieck.ι (sliceDiagram U) (op n))
    (overFppfTopology X) ((fppfTopology S).over (U.obj (op n)))
    (sliceTotalTopology (fppfTopology S) U) ((fppfTopology S).overPullback_isContinuous _) hι

set_option backward.isDefEq.respectTransparency false in
/-- A coface induces the cartesian arrow between the corresponding pullbacks. -/
private def fppfCofaceArrow (V : Over X) (i : Fin 2) :
    (fppfAugmentationStage U a ⦋1⦌).obj V ⟶
      (fppfAugmentationStage U a ⦋0⦌).obj V where
  base := (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌).op
  fiber := Over.homMk
    (pullback.lift (pullback.fst V.hom (a.app (op ⦋1⦌)))
      (pullback.snd V.hom (a.app (op ⦋1⦌)) ≫ U.map (SimplexCategory.δ i).op)
      (by
        rw [Category.assoc, (a.naturality (SimplexCategory.δ i).op).trans (Category.comp_id _)]
        exact pullback.condition))
    (pullback.lift_snd _ _ _)

/-- The cartesian coface arrows are natural in the object over the augmentation target. -/
private abbrev FppfCofaceLaw : Prop :=
  ∀ (i : Fin 2) {V W : Over X} (f : V ⟶ W),
    (fppfAugmentationStage U a ⦋1⦌).map f ≫ fppfCofaceArrow U a W i =
      fppfCofaceArrow U a V i ≫ (fppfAugmentationStage U a ⦋0⦌).map f

/-- The cartesian arrows form a natural transformation between the two stage pullbacks. -/
private def fppfCoface (hc : FppfCofaceLaw U a) (i : Fin 2) :
    fppfAugmentationStage U a ⦋1⦌ ⟶ fppfAugmentationStage U a ⦋0⦌ where
  app V := fppfCofaceArrow U a V i
  naturality _ _ f := hc i f

/-- The natural coface restriction on direct-image functors. -/
private def fppfParallelNat (hc : FppfCofaceLaw U a)
    (A : Type (u+1)) [Category.{u} A] (i : Fin 2) :
    (fppfAugmentationStage U a ⦋0⦌).sheafPushforwardContinuous A
      (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U) ⟶
    (fppfAugmentationStage U a ⦋1⦌).sheafPushforwardContinuous A
      (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  Functor.sheafPushforwardContinuousNatTrans (fppfCoface U a hc i) A
    (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)

/-- Restriction along cartesian cofaces gives the two arrows on stage direct images. -/
private def fppfParallelCore (hc : FppfCofaceLaw U a)
    (A : Type (u + 1)) [Category.{u} A]
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) A) (i : Fin 2) :=
  (fppfParallelNat U a hc A i).app F

/-- The direct-image functor is the equalizer of the two coface restrictions. -/
private def fppfDirectImageCore (hc : FppfCofaceLaw U a)
    (A : Type (u + 1)) [Category.{u} A]
    [HasLimitsOfShape WalkingParallelPair (Sheaf (overFppfTopology X) A)] :
    Sheaf (sliceTotalTopology (fppfTopology S) U) A ⥤ Sheaf (overFppfTopology X) A where
  obj F := equalizer (fppfParallelCore U a hc A F 0)
    (fppfParallelCore U a hc A F 1)
  map {F G} α := equalizer.lift
    (equalizer.ι (fppfParallelCore U a hc A F 0)
      (fppfParallelCore U a hc A F 1) ≫
      ((fppfAugmentationStage U a ⦋0⦌).sheafPushforwardContinuous A
        (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)).map α)
    (by
      have h0 := (fppfParallelNat U a hc A 0).naturality α
      have h1 := (fppfParallelNat U a hc A 1).naturality α
      change _ ≫ fppfParallelCore U a hc A G 0 =
        fppfParallelCore U a hc A F 0 ≫ _ at h0
      change _ ≫ fppfParallelCore U a hc A G 1 =
        fppfParallelCore U a hc A F 1 ≫ _ at h1
      rw [Category.assoc, h0, ← Category.assoc, equalizer.condition,
        Category.assoc, ← h1, ← Category.assoc])
  map_id := by
    intro F
    apply equalizer.hom_ext
    rw [equalizer.lift_ι, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  map_comp := by
    intro F G H α β
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι, CategoryTheory.Functor.map_comp]
    simp only [← Category.assoc, equalizer.lift_ι]

/-- Restriction along all augmentation components preserves the sheaf condition. -/
private abbrev FppfInverseSheafLaw : Prop :=
  ∀ G : Sheaf (overFppfTopology X) (Type u),
    Presheaf.IsSheaf (sliceTotalTopology (fppfTopology S) U) ((sliceForget U a).op ⋙ G.obj)

/-- The augmentation inverse image is actual restriction along all augmentation components. -/
private def fppfAugmentationInverseImage (hs : FppfInverseSheafLaw U a) :
    Sheaf (overFppfTopology X) (Type u) ⥤
      Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u) where
  obj G := ⟨(sliceForget U a).op ⋙ G.obj, hs G⟩
  map α := ObjectProperty.homMk (Functor.whiskerLeft (sliceForget U a).op α.hom)
  map_id := by intro G; rfl
  map_comp := by intro G H K α β; rfl

/-- The projection from a stagewise cartesian object to the object over the target. -/
private def fppfStageProjection (V : Over X) (n : SimplexCategory) :
    (sliceForget U a).obj ((fppfAugmentationStage U a n).obj V) ⟶ V :=
  Over.homMk (pullback.fst V.hom (a.app (op n))) pullback.condition

set_option backward.isDefEq.respectTransparency false in
/-- Every total object maps canonically to the degree-zero cartesian object over its image. -/
private def fppfReconstructionArrow (Y : sliceTotalSite U) :
    Y ⟶ (fppfAugmentationStage U a ⦋0⦌).obj ((sliceForget U a).obj Y) where
  base := (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op
  fiber := Over.homMk
    (pullback.lift (𝟙 Y.fiber.left)
      (Y.fiber.hom ≫ U.map (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op)
      (by
        change (𝟙 Y.fiber.left) ≫ (Y.fiber.hom ≫ a.app Y.base) = _
        exact (Category.id_comp _).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun f ↦ Y.fiber.hom ≫ f)
              ((a.naturality (SimplexCategory.const ⦋0⦌ Y.base.unop 0).op).trans
                (Category.comp_id _)))).symm))
    (pullback.lift_snd _ _ _)

/-- The degree-zero formula for the forward augmentation adjunction map. -/
private def fppfHomToApp (hs : FppfInverseSheafLaw U a)
    (G : Sheaf (overFppfTopology X) (Type u))
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (α : (fppfAugmentationInverseImage U a hs).obj G ⟶ F) (V : (Over X)ᵒᵖ) :=
  G.obj.map (fppfStageProjection U a V.unop ⦋0⦌).op ≫
    α.hom.app (op ((fppfAugmentationStage U a ⦋0⦌).obj V.unop)) ≫
    (Functor.sheafPushforwardContinuousObjObjIso (fppfAugmentationStage U a ⦋0⦌)
      (J := overFppfTopology X) (Type u) F V.unop).inv

/-- The forward formula respects restriction and equalizes the two coface arrows. -/
private abbrev FppfHomToLaw (hc : FppfCofaceLaw U a) (hs : FppfInverseSheafLaw U a) : Prop :=
  ∀ (G : Sheaf (overFppfTopology X) (Type u))
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (α : (fppfAugmentationInverseImage U a hs).obj G ⟶ F),
    (∀ {V W : (Over X)ᵒᵖ} (f : V ⟶ W),
      G.obj.map f ≫ fppfHomToApp U a hs G F α W =
        fppfHomToApp U a hs G F α V ≫
          (((fppfAugmentationStage U a ⦋0⦌).sheafPushforwardContinuous (Type u)
            (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)).obj F).obj.map f) ∧
    (∀ V : (Over X)ᵒᵖ,
      fppfHomToApp U a hs G F α V ≫ (fppfParallelCore U a hc (Type u) F 0).hom.app V =
      fppfHomToApp U a hs G F α V ≫ (fppfParallelCore U a hc (Type u) F 1).hom.app V)

/-- The forward adjunction map factors the restriction formula through the coface equalizer. -/
private def fppfHomTo (hc : FppfCofaceLaw U a) (hs : FppfInverseSheafLaw U a)
    (ht : FppfHomToLaw U a hc hs)
    (G : Sheaf (overFppfTopology X) (Type u))
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (α : (fppfAugmentationInverseImage U a hs).obj G ⟶ F) :
    G ⟶ (fppfDirectImageCore U a hc (Type u)).obj F :=
  equalizer.lift
    (show G ⟶ ((fppfAugmentationStage U a ⦋0⦌).sheafPushforwardContinuous (Type u)
      (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)).obj F from
      ObjectProperty.homMk
        { app := fppfHomToApp U a hs G F α
          naturality := fun _ _ f ↦ (ht G F α).1 f })
    (by ext V x; exact ConcreteCategory.congr_hom ((ht G F α).2 V) x)

/-- The inverse adjunction formula reconstructs a section at each total object. -/
private def fppfHomInvApp (hc : FppfCofaceLaw U a)
    (G : Sheaf (overFppfTopology X) (Type u))
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (β : G ⟶ (fppfDirectImageCore U a hc (Type u)).obj F)
    (Y : (sliceTotalSite U)ᵒᵖ) :=
  β.hom.app (op ((sliceForget U a).obj Y.unop)) ≫
    (equalizer.ι (fppfParallelCore U a hc (Type u) F 0)
      (fppfParallelCore U a hc (Type u) F 1)).hom.app
        (op ((sliceForget U a).obj Y.unop)) ≫
    (Functor.sheafPushforwardContinuousObjObjIso (fppfAugmentationStage U a ⦋0⦌)
      (J := overFppfTopology X) (Type u) F ((sliceForget U a).obj Y.unop)).hom ≫
    F.obj.map (fppfReconstructionArrow U a Y.unop).op

/-- Reconstruction commutes with every total restriction map. -/
private abbrev FppfHomInvLaw (hc : FppfCofaceLaw U a) (hs : FppfInverseSheafLaw U a) : Prop :=
  ∀ (G : Sheaf (overFppfTopology X) (Type u))
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (β : G ⟶ (fppfDirectImageCore U a hc (Type u)).obj F)
    {Y Z : (sliceTotalSite U)ᵒᵖ} (f : Y ⟶ Z),
    ((fppfAugmentationInverseImage U a hs).obj G).obj.map f ≫ fppfHomInvApp U a hc G F β Z =
      fppfHomInvApp U a hc G F β Y ≫ F.obj.map f

/-- The inverse adjunction map assembles the explicit section reconstruction. -/
private def fppfHomInv (hc : FppfCofaceLaw U a) (hs : FppfInverseSheafLaw U a)
    (hi : FppfHomInvLaw U a hc hs)
    (G : Sheaf (overFppfTopology X) (Type u))
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    (β : G ⟶ (fppfDirectImageCore U a hc (Type u)).obj F) :
    (fppfAugmentationInverseImage U a hs).obj G ⟶ F :=
  ObjectProperty.homMk
    { app := fppfHomInvApp U a hc G F β
      naturality := fun _ _ f ↦ hi G F β f }

/-- The canonical restriction and reconstruction formulas are inverse natural Hom maps,
and augmentation restriction is left exact. -/
theorem fppfAugmentation_laws :
    FppfCofaceLaw U a ∧ FppfInverseSheafLaw U a ∧
    ∀ (hc : FppfCofaceLaw U a) (hs : FppfInverseSheafLaw U a),
    (FppfHomToLaw U a hc hs ∧ FppfHomInvLaw U a hc hs) ∧
    (∀ (ht : FppfHomToLaw U a hc hs) (hi : FppfHomInvLaw U a hc hs)
      (G : Sheaf (overFppfTopology X) (Type u))
      (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)),
      Function.LeftInverse (fppfHomInv U a hc hs hi G F) (fppfHomTo U a hc hs ht G F) ∧
      Function.RightInverse (fppfHomInv U a hc hs hi G F) (fppfHomTo U a hc hs ht G F)) ∧
    (∀ (ht : FppfHomToLaw U a hc hs) (hi : FppfHomInvLaw U a hc hs),
      (∀ {G' G : Sheaf (overFppfTopology X) (Type u)}
        {F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)}
        (f : G' ⟶ G) (g : G ⟶ (fppfDirectImageCore U a hc (Type u)).obj F),
        fppfHomInv U a hc hs hi G' F (f ≫ g) =
          (fppfAugmentationInverseImage U a hs).map f ≫ fppfHomInv U a hc hs hi G F g) ∧
      (∀ {G : Sheaf (overFppfTopology X) (Type u)}
        {F F' : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)}
        (f : (fppfAugmentationInverseImage U a hs).obj G ⟶ F) (g : F ⟶ F'),
        fppfHomTo U a hc hs ht G F' (f ≫ g) =
          fppfHomTo U a hc hs ht G F f ≫ (fppfDirectImageCore U a hc (Type u)).map g)) ∧
    PreservesFiniteLimits (fppfAugmentationInverseImage U a hs) := by
  sorry

/-- The total fppf augmentation uses every augmentation component and has coface-equalizer direct image. -/
def fppfAugmentation :
    MorphismOfTopoiIn.{u+1,u+1,u+1,u+1,u} (overFppfTopology X)
      (sliceTotalTopology (fppfTopology S) U) where
  inverseImageFunctor := ⟨fppfAugmentationInverseImage U a (fppfAugmentation_laws U a).2.1,
    ((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).2.2.2⟩
  pushforward := fppfDirectImageCore U a (fppfAugmentation_laws U a).1 (Type u)
  adjunction := Adjunction.mkOfHomEquiv
    { homEquiv := fun G F ↦
        { toFun := fppfHomTo U a (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).1 G F
          invFun := fppfHomInv U a (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).2 G F
          left_inv := (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).2.1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).2 G F).1
          right_inv := (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).2.1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).2 G F).2 }
      homEquiv_naturality_left_symm :=
        (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).2.2.1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).2).1
      homEquiv_naturality_right :=
        (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).2.2.1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).1 (((fppfAugmentation_laws U a).2.2 (fppfAugmentation_laws U a).1 (fppfAugmentation_laws U a).2.1).1).2).2 }


/-- The canonical coface restrictions on stage direct images. -/
def fppfAugmentationParallel (A : Type (u+1)) [Category.{u} A]
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) A) (i : Fin 2) :=
  fppfParallelCore U a (fppfAugmentation_laws U a).1 A F i

/-- The canonical two-coface equalizer functor for arbitrary coefficients admitting equalizers. -/
def fppfAugmentationDirectImage (A : Type (u+1)) [Category.{u} A]
    [HasLimitsOfShape WalkingParallelPair (Sheaf (overFppfTopology X) A)] :=
  fppfDirectImageCore U a (fppfAugmentation_laws U a).1 A

/-- Total fppf augmentation inverse image is restriction along all augmentation components. -/
theorem fppfAugmentation_inverseImage_obj
    (G : Sheaf (overFppfTopology X) (Type u)) (Y : sliceTotalSite U) :
    ((fppfAugmentation U a)⁻¹.obj G).obj.obj (op Y) =
      G.obj.obj (op ((sliceForget U a).obj Y)) := rfl

/-- Total fppf augmentation direct image retains the two-coface equalizer condition. -/
theorem fppfAugmentation_pushforward_obj
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)) :
    (fppfAugmentation U a).pushforward.obj F =
      equalizer (fppfAugmentationParallel U a (Type u) F 0)
        (fppfAugmentationParallel U a (Type u) F 1) := rfl

/-- Stage direct image of the restriction of a total fppf sheaf to total étale objects. -/
private def squareEtaleStage (n : SimplexCategory) :=
  (fppfEtaleComparison U).pushforward ⋙ spacesEtaleRestrict U n ⋙
    (spacesRingedMorphismOfTopoi (a.app (op n))).pushforward

/-- Stage direct image on the fppf side, restricted to étale objects over the target. -/
private def squareFppfStage (n : SimplexCategory) :=
  (fppfAugmentationStage U a n).sheafPushforwardContinuous (Type u)
    (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U) ⋙
      (Fppf.SmallCoefficients.spacesComparison X).pushforward

/-- The two stage presentations have identical section carriers and compatible restriction maps. -/
private abbrev SquareStageLaw : Prop :=
  ∀ (n : SimplexCategory) (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u))
    {V W : (spacesEtaleSite X)ᵒᵖ} (f : V ⟶ W),
    (((squareEtaleStage U a n).obj F).obj.map f ≫ (↾fun x ↦ x) =
      (↾fun x ↦ x) ≫ ((squareFppfStage U a n).obj F).obj.map f) ∧
    (((squareFppfStage U a n).obj F).obj.map f ≫ (↾fun x ↦ x) =
      (↾fun x ↦ x) ≫ ((squareEtaleStage U a n).obj F).obj.map f)

/-- The stage comparison is identity on sections of the common cartesian object. -/
private def squareStageTo (hs : SquareStageLaw U a)
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)) (n : SimplexCategory) :
    (squareEtaleStage U a n).obj F ⟶ (squareFppfStage U a n).obj F :=
  ObjectProperty.homMk
    { app := fun _ ↦ ↾fun x ↦ x
      naturality := fun _ _ f ↦ (hs n F f).1 }

/-- The reverse stage comparison is identity on the same cartesian sections. -/
private def squareStageInv (hs : SquareStageLaw U a)
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)) (n : SimplexCategory) :
    (squareFppfStage U a n).obj F ⟶ (squareEtaleStage U a n).obj F :=
  ObjectProperty.homMk
    { app := fun _ ↦ ↾fun x ↦ x
      naturality := fun _ _ f ↦ (hs n F f).2 }

/-- The total étale route around the direct-image square. -/
private def squareEtaleRight :=
  (fppfEtaleComparison U).pushforward ⋙ (spacesEtaleAugmentation U a).pushforward

/-- The total fppf route around the direct-image square. -/
private def squareFppfRight :=
  (fppfAugmentation U a).pushforward ⋙ (Fppf.SmallCoefficients.spacesComparison X).pushforward

/-- Étale restriction commutes canonically with the fppf coface equalizer. -/
private def squareRestrictionEqualizerIso
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)) :
    (squareFppfRight U a).obj F ≅
      equalizer
        ((Fppf.SmallCoefficients.spacesComparison X).pushforward.map
          (fppfAugmentationParallel U a (Type u) F 0))
        ((Fppf.SmallCoefficients.spacesComparison X).pushforward.map
          (fppfAugmentationParallel U a (Type u) F 1)) :=
  @PreservesEqualizer.iso _ _ _ _
    (Fppf.SmallCoefficients.spacesComparison X).pushforward _ _ _ _
    inferInstance inferInstance
    ((((Fppf.SmallCoefficients.spacesComparison X).adjunction.rightAdjoint_preservesLimits).preservesLimitsOfShape).preservesLimit)

/-- The common stage comparisons transport both coface equalizer conditions. -/
private abbrev SquareEqualizerLaw (hs : SquareStageLaw U a) : Prop :=
  ∀ F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u),
    ((equalizer.ι
        (spacesEtaleAugmentationParallel U a ((fppfEtaleComparison U).pushforward.obj F) 0)
        (spacesEtaleAugmentationParallel U a ((fppfEtaleComparison U).pushforward.obj F) 1) ≫
      squareStageTo U a hs F ⦋0⦌) ≫
        (Fppf.SmallCoefficients.spacesComparison X).pushforward.map
          (fppfAugmentationParallel U a (Type u) F 0) =
    (equalizer.ι
        (spacesEtaleAugmentationParallel U a ((fppfEtaleComparison U).pushforward.obj F) 0)
        (spacesEtaleAugmentationParallel U a ((fppfEtaleComparison U).pushforward.obj F) 1) ≫
      squareStageTo U a hs F ⦋0⦌) ≫
        (Fppf.SmallCoefficients.spacesComparison X).pushforward.map
          (fppfAugmentationParallel U a (Type u) F 1)) ∧
    (((Fppf.SmallCoefficients.spacesComparison X).pushforward.map
      (equalizer.ι
        (fppfAugmentationParallel U a (Type u) F 0)
        (fppfAugmentationParallel U a (Type u) F 1)) ≫
      squareStageInv U a hs F ⦋0⦌) ≫
        spacesEtaleAugmentationParallel U a ((fppfEtaleComparison U).pushforward.obj F) 0 =
    ((Fppf.SmallCoefficients.spacesComparison X).pushforward.map
      (equalizer.ι
        (fppfAugmentationParallel U a (Type u) F 0)
        (fppfAugmentationParallel U a (Type u) F 1)) ≫
      squareStageInv U a hs F ⦋0⦌) ≫
        spacesEtaleAugmentationParallel U a ((fppfEtaleComparison U).pushforward.obj F) 1)

/-- The forward square map factors the common stage section through the fppf equalizer. -/
private def squareForward (hs : SquareStageLaw U a) (he : SquareEqualizerLaw U a hs)
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)) :
    (squareEtaleRight U a).obj F ⟶ (squareFppfRight U a).obj F :=
  equalizer.lift
    (equalizer.ι
      (spacesEtaleAugmentationParallel U a ((fppfEtaleComparison U).pushforward.obj F) 0)
      (spacesEtaleAugmentationParallel U a ((fppfEtaleComparison U).pushforward.obj F) 1) ≫
      squareStageTo U a hs F ⦋0⦌) (he F).1 ≫
    (squareRestrictionEqualizerIso U a F).inv

/-- The reverse square map factors the common stage section through the étale equalizer. -/
private def squareBackward (hs : SquareStageLaw U a) (he : SquareEqualizerLaw U a hs)
    (F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)) :
    (squareFppfRight U a).obj F ⟶ (squareEtaleRight U a).obj F :=
  equalizer.lift
    ((Fppf.SmallCoefficients.spacesComparison X).pushforward.map
      (equalizer.ι
        (fppfAugmentationParallel U a (Type u) F 0)
        (fppfAugmentationParallel U a (Type u) F 1)) ≫
      squareStageInv U a hs F ⦋0⦌) (he F).2

/-- Canonical stage section identifications commute with cofaces and give inverse natural comparisons
between the two total augmentation direct images. -/
theorem fppfEtaleCommSq_laws :
    SquareStageLaw U a ∧ ∀ hs : SquareStageLaw U a,
    SquareEqualizerLaw U a hs ∧ ∀ he : SquareEqualizerLaw U a hs,
    (∀ F : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u),
      squareForward U a hs he F ≫ squareBackward U a hs he F = 𝟙 _ ∧
      squareBackward U a hs he F ≫ squareForward U a hs he F = 𝟙 _) ∧
    (∀ {F G : Sheaf (sliceTotalTopology (fppfTopology S) U) (Type u)} (α : F ⟶ G),
      (squareEtaleRight U a).map α ≫ squareForward U a hs he G =
        squareForward U a hs he F ≫ (squareFppfRight U a).map α) := by
  sorry

/-- The canonical isomorphism of direct images around the total comparison square. -/
def fppfEtaleDirectImageSquare : squareEtaleRight U a ≅ squareFppfRight U a :=
  NatIso.ofComponents (fun F ↦
    { hom := squareForward U a (fppfEtaleCommSq_laws U a).1
        ((fppfEtaleCommSq_laws U a).2 (fppfEtaleCommSq_laws U a).1).1 F
      inv := squareBackward U a (fppfEtaleCommSq_laws U a).1
        ((fppfEtaleCommSq_laws U a).2 (fppfEtaleCommSq_laws U a).1).1 F
      hom_inv_id := (((fppfEtaleCommSq_laws U a).2 (fppfEtaleCommSq_laws U a).1).2
        ((fppfEtaleCommSq_laws U a).2 (fppfEtaleCommSq_laws U a).1).1).1 F |>.1
      inv_hom_id := (((fppfEtaleCommSq_laws U a).2 (fppfEtaleCommSq_laws U a).1).2
        ((fppfEtaleCommSq_laws U a).2 (fppfEtaleCommSq_laws U a).1).1).1 F |>.2 })
    (((fppfEtaleCommSq_laws U a).2 (fppfEtaleCommSq_laws U a).1).2
      ((fppfEtaleCommSq_laws U a).2 (fppfEtaleCommSq_laws U a).1).1).2

/-- The canonical comparison of inverse images for an arbitrary augmented simplicial algebraic space. -/
def fppfEtaleCommSq :
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (fppfEtaleComparison U)⁻¹ ≅
      (Fppf.SmallCoefficients.spacesComparison X)⁻¹ ⋙ (fppfAugmentation U a)⁻¹ :=
  Adjunction.leftAdjointCompIso (spacesEtaleAugmentation U a).adjunction
    (fppfEtaleComparison U).adjunction
    ((Fppf.SmallCoefficients.spacesComparison X).adjunction.comp (fppfAugmentation U a).adjunction)
    (fppfEtaleDirectImageSquare U a)

end AlgebraicGeometry.AlgebraicSpace.Simplicial.SmallCoefficients

end
