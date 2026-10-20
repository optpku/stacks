/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.AffineCoverBasis
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesAtlasCharts
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfComparison
public import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Small matching-family quotients for the fppf topology -/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace.Fppf.AffineCoverBasis

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Fppf.SmallCoefficients

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Matching sections on an affine covering satisfy the equations on every pairwise fibre product. -/
def Matching (P : (Over X)ᵒᵖ ⥤ Type u) {V : Over X} (B : Cover V.left) : Type u :=
  {s : ∀ c : B.val, P.obj (op (overChart V c.val)) //
    ∀ b c : B.val,
      P.map (pullback.fst (overChartMap V b.val) (overChartMap V c.val)).op (s b) =
        P.map (pullback.snd (overChartMap V b.val) (overChartMap V c.val)).op (s c)}

/-- A matching family has equal restrictions along any two arrows with the same composite. -/
private theorem matching_cone (P : (Over X)ᵒᵖ ⥤ Type u) {V : Over X}
    {B : Cover V.left} (s : Matching P B) (b c : B.val) {W : Over X}
    (f : W ⟶ overChart V b.val) (g : W ⟶ overChart V c.val)
    (h : f ≫ overChartMap V b.val = g ≫ overChartMap V c.val) :
    P.map f.op (s.val b) = P.map g.op (s.val c) := by
  have e := congrArg (fun x ↦
    P.map (pullback.lift f g h).op x) (s.property b c)
  simpa only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
    pullback.lift_fst, pullback.lift_snd] using e

/-- Two matching families agree if they agree after some further covering refinement. -/
def plusRel (P : (Over X)ᵒᵖ ⥤ Type u) (V : Over X)
    (s t : Σ B : Cover V.left, Matching P B) : Prop :=
  ∃ D : Cover V.left,
    (∀ d : D.val, ∃ b : s.1.val, Nonempty (Lift (𝟙 V.left) d.val b.val)) ∧
    (∀ d : D.val, ∃ c : t.1.val, Nonempty (Lift (𝟙 V.left) d.val c.val)) ∧
    ∀ (d : D.val) (b : s.1.val) (c : t.1.val)
      (l : Lift (𝟙 V.left) d.val b.val) (k : Lift (𝟙 V.left) d.val c.val),
      P.map (overLiftMap (𝟙 V) l).op (s.2.val b) =
        P.map (overLiftMap (𝟙 V) k).op (t.2.val c)

/-- Pullback along every qualifying factorization determines a unique section. -/
private theorem restrictionValue_existsUnique (P : (Over X)ᵒᵖ ⥤ Type u)
    {V W : Over X} (f : V ⟶ W) {B : Cover W.left} (s : Matching P B)
    (d : (pullbackCover f.left B).val) :
    ∃! x : P.obj (op (overChart V d.val)),
      ∀ (b : B.val) (l : Lift f.left d.val b.val),
        P.map (overLiftMap f l).op (s.val b) = x := by
  obtain ⟨b, ⟨l⟩⟩ := d.property
  refine ⟨P.map (overLiftMap f l).op (s.val b), ?_, ?_⟩
  · intro c k
    apply matching_cone P s c b (overLiftMap f k) (overLiftMap f l)
    apply Over.OverMorphism.ext
    change liftMap k ≫ (chart c.val).hom = liftMap l ≫ (chart b.val).hom
    rw [liftMap_w, liftMap_w]
  · intro x hx
    exact (hx b l).symm

/-- The unique restriction value characterized by all coded lifts. -/
private def restrictionValue (P : (Over X)ᵒᵖ ⥤ Type u)
    {V W : Over X} (f : V ⟶ W) {B : Cover W.left} (s : Matching P B)
    (d : (pullbackCover f.left B).val) : P.obj (op (overChart V d.val)) :=
  (restrictionValue_existsUnique P f s d).choose

/-- Restriction of a matching family uses the unique values specified by all its lifts. -/
private def restrictMatching (P : (Over X)ᵒᵖ ⥤ Type u)
    {V W : Over X} (f : V ⟶ W) {B : Cover W.left} (s : Matching P B) :
    Matching P (pullbackCover f.left B) :=
  ⟨restrictionValue P f s, by
    intro d e
    obtain ⟨b, ⟨l⟩⟩ := d.property
    obtain ⟨c, ⟨k⟩⟩ := e.property
    dsimp only [restrictionValue]
    rw [← (restrictionValue_existsUnique P f s d).choose_spec.1 b l,
      ← (restrictionValue_existsUnique P f s e).choose_spec.1 c k]
    simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp]
    apply matching_cone P s b c
    simp only [Category.assoc, overLiftMap_w]
    rw [← Category.assoc, pullback.condition, Category.assoc]⟩

/-- Pullback acts on the disjoint union of matching families over all small covers. -/
private def restrictRepresentative (P : (Over X)ᵒᵖ ⥤ Type u)
    {V W : Over X} (f : V ⟶ W) (s : Σ B : Cover W.left, Matching P B) :
    Σ B : Cover V.left, Matching P B :=
  ⟨pullbackCover f.left s.1, restrictMatching P f s.2⟩

/-- A morphism of presheaves acts componentwise on matching sections. -/
private def mapMatching {P Q : (Over X)ᵒᵖ ⥤ Type u} (α : P ⟶ Q)
    {V : Over X} {B : Cover V.left} (s : Matching P B) : Matching Q B :=
  ⟨fun c ↦ α.app _ (s.val c), by
    intro b c
    have e := congrArg (α.app _) (s.property b c)
    simpa only [ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom (α.naturality
        (pullback.fst (overChartMap V b.val) (overChartMap V c.val)).op) (s.val b)).symm.trans
        (e.trans (ConcreteCategory.congr_hom (α.naturality
          (pullback.snd (overChartMap V b.val) (overChartMap V c.val)).op) (s.val c)))⟩

/-- A section determines its family of restrictions to all affine charts. -/
private def unitRepresentative (P : (Over X)ᵒᵖ ⥤ Type u) (V : Over X)
    (x : P.obj (op V)) : Σ B : Cover V.left, Matching P B :=
  ⟨allCharts V.left, ⟨fun c ↦ P.map (overChartMap V c.val).op x, by
    intro b c
    simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp,
      pullback.condition]⟩⟩

/-- Refinement equivalence is compatible with restriction, presheaf morphisms, and the section unit. -/
theorem plus_relation_laws :
    (∀ (P : (Over X)ᵒᵖ ⥤ Type u) (V : Over X), Equivalence (plusRel P V)) ∧
    (∀ (P : (Over X)ᵒᵖ ⥤ Type u) {V W : Over X} (f : V ⟶ W)
      (s t : Σ B : Cover W.left, Matching P B), plusRel P W s t →
        plusRel P V (restrictRepresentative P f s) (restrictRepresentative P f t)) ∧
    (∀ (P : (Over X)ᵒᵖ ⥤ Type u) (V : Over X) (s : Σ B : Cover V.left, Matching P B),
      plusRel P V (restrictRepresentative P (𝟙 V) s) s) ∧
    (∀ (P : (Over X)ᵒᵖ ⥤ Type u) {V W Z : Over X} (f : V ⟶ W) (g : W ⟶ Z)
      (s : Σ B : Cover Z.left, Matching P B),
      plusRel P V (restrictRepresentative P (f ≫ g) s)
        (restrictRepresentative P f (restrictRepresentative P g s))) ∧
    (∀ {P Q : (Over X)ᵒᵖ ⥤ Type u} (α : P ⟶ Q) (V : Over X)
      (s t : Σ B : Cover V.left, Matching P B), plusRel P V s t →
        plusRel Q V ⟨s.1, mapMatching α s.2⟩ ⟨t.1, mapMatching α t.2⟩) ∧
    (∀ (P : (Over X)ᵒᵖ ⥤ Type u) {V W : Over X} (f : V ⟶ W) (x : P.obj (op W)),
      plusRel P V (restrictRepresentative P f (unitRepresentative P W x))
        (unitRepresentative P V (P.map f.op x))) := by
  sorry

/-- The quotient of small matching families by agreement on a covering refinement. -/
def Plus (P : (Over X)ᵒᵖ ⥤ Type u) (V : Over X) : Type u :=
  Quotient ⟨plusRel P V, (plus_relation_laws (X := X)).1 P V⟩

/-- Restriction in the matching-family quotient is induced by all-factorization pullback. -/
private def plusRestriction (P : (Over X)ᵒᵖ ⥤ Type u) {V W : Over X}
    (f : V ⟶ W) : Plus P W → Plus P V :=
  Quotient.map (restrictRepresentative P f) ((plus_relation_laws (X := X)).2.1 P f)

/-- The matching-family quotient is a presheaf with values in the original universe. -/
def plusObj (P : (Over X)ᵒᵖ ⥤ Type u) : (Over X)ᵒᵖ ⥤ Type u where
  obj V := Plus P V.unop
  map f := ↾(plusRestriction P f.unop)
  map_id V := by
    ext x
    refine Quotient.inductionOn x ?_
    intro s
    exact Quotient.sound ((plus_relation_laws (X := X)).2.2.1 P V.unop s)
  map_comp f g := by
    ext x
    refine Quotient.inductionOn x ?_
    intro s
    exact Quotient.sound ((plus_relation_laws (X := X)).2.2.2.1 P g.unop f.unop s)

/-- The unit sends a section to its restrictions on every affine chart. -/
def toPlus (P : (Over X)ᵒᵖ ⥤ Type u) : P ⟶ plusObj P where
  app V := ↾fun x ↦ Quotient.mk _ (unitRepresentative P V.unop x)
  naturality {V W} f := by
    ext x
    exact (Quotient.sound ((plus_relation_laws (X := X)).2.2.2.2.2 P f.unop x)).symm

/-- A presheaf morphism acts on the matching-family quotient by its component maps. -/
def plusMap {P Q : (Over X)ᵒᵖ ⥤ Type u} (α : P ⟶ Q) : plusObj P ⟶ plusObj Q where
  app V := ↾(Quotient.map (fun s ↦ ⟨s.1, mapMatching α s.2⟩)
    ((plus_relation_laws (X := X)).2.2.2.2.1 α V.unop))
  naturality {V W} f := by
    ext x
    refine Quotient.inductionOn x ?_
    intro s
    apply congrArg (Quotient.mk _)
    apply congrArg (Sigma.mk (pullbackCover f.unop.left s.1))
    apply Subtype.ext
    funext d
    obtain ⟨b, ⟨l⟩⟩ := d.property
    change α.app _ (restrictionValue P f.unop s.2 d) =
      restrictionValue Q f.unop (mapMatching α s.2) d
    dsimp only [restrictionValue]
    rw [← (restrictionValue_existsUnique P f.unop s.2 d).choose_spec.1 b l,
      ← (restrictionValue_existsUnique Q f.unop (mapMatching α s.2) d).choose_spec.1 b l]
    exact ConcreteCategory.congr_hom (α.naturality (overLiftMap f.unop l).op) (s.2.val b)

/-- Taking matching-family quotients is functorial in the presheaf. -/
def plusFunctor : ((Over X)ᵒᵖ ⥤ Type u) ⥤ ((Over X)ᵒᵖ ⥤ Type u) where
  obj := plusObj
  map := plusMap
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

/-- Applying the matching-family quotient twice yields an fppf sheaf. -/
theorem sheafification_laws (P : (Over X)ᵒᵖ ⥤ Type u) :
    Presheaf.IsSheaf (overFppfTopology X) (plusObj (plusObj P)) := by
  sorry

/-- Sheafification in the original universe is the twofold matching-family quotient. -/
def sheafification : ((Over X)ᵒᵖ ⥤ Type u) ⥤ Sheaf (overFppfTopology X) (Type u) where
  obj P := ⟨plusObj (plusObj P), sheafification_laws P⟩
  map α := ObjectProperty.homMk (plusMap (plusMap α))
  map_id P := by
    apply ObjectProperty.hom_ext
    exact (plusFunctor (X := X) ⋙ plusFunctor).map_id P
  map_comp α β := by
    apply ObjectProperty.hom_ext
    exact (plusFunctor (X := X) ⋙ plusFunctor).map_comp α β

/-- The sheafification unit is the composite of the two restriction-family units. -/
def sheafificationUnit (P : (Over X)ᵒᵖ ⥤ Type u) :
    P ⟶ (sheafification.obj P).obj :=
  toPlus P ≫ toPlus (plusObj P)

/-- An affine covering of the source object remains covering in every ambient slice. -/
private theorem coverInSlice (V : Over X) (B : Cover V.left) :
    Sieve.ofArrows (fun c : B.val ↦ overChart V c.val)
      (fun c ↦ overChartMap V c.val) ∈ overFppfTopology X V := by
  rw [overFppfTopology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact B.property

/-- Amalgamate a matching family after applying a presheaf morphism to a sheaf. -/
private def amalgamateMatching {P : (Over X)ᵒᵖ ⥤ Type u}
    (F : Sheaf (overFppfTopology X) (Type u)) (α : P ⟶ F.obj)
    {V : Over X} {B : Cover V.left} (s : Matching P B) : F.obj.obj (op V) :=
  (F.property.amalgamateOfArrows (fun c : B.val ↦ overChartMap V c.val)
    (coverInSlice V B)
    (fun c ↦ (↾fun _ : PUnit.{u + 1} ↦ α.app _ (s.val c)))
    (by
      intro W b c f g h
      ext x
      have e := matching_cone P s b c f g h
      exact (ConcreteCategory.congr_hom (α.naturality f.op) (s.val b)).symm.trans
        ((congrArg (α.app _) e).trans
          (ConcreteCategory.congr_hom (α.naturality g.op) (s.val c))))) PUnit.unit

/-- Unique amalgamation is independent of refinement and commutes with restriction. -/
private def GluingLaws (X : AlgebraicSpace S) : Prop :=
  (∀ {P : (Over X)ᵒᵖ ⥤ Type u} (F : Sheaf (overFppfTopology X) (Type u))
    (α : P ⟶ F.obj) (V : Over X) (s t : Σ B : Cover V.left, Matching P B),
    plusRel P V s t → amalgamateMatching F α s.2 = amalgamateMatching F α t.2) ∧
  (∀ {P : (Over X)ᵒᵖ ⥤ Type u} (F : Sheaf (overFppfTopology X) (Type u))
    (α : P ⟶ F.obj) {V W : Over X} (f : V ⟶ W)
    (s : Σ B : Cover W.left, Matching P B),
    amalgamateMatching F α (restrictRepresentative P f s).2 =
      F.obj.map f.op (amalgamateMatching F α s.2))

/-- Extension to the matching-family quotient uses the target sheaf's unique amalgamation. -/
private def plusLift (h : GluingLaws X) {P : (Over X)ᵒᵖ ⥤ Type u}
    (F : Sheaf (overFppfTopology X) (Type u)) (α : P ⟶ F.obj) : plusObj P ⟶ F.obj where
  app V := ↾(Quotient.lift (fun s ↦ amalgamateMatching F α s.2) (h.1 F α V.unop))
  naturality {V W} f := by
    ext x
    refine Quotient.inductionOn x ?_
    intro s
    exact h.2 F α f.unop s

/-- A map from a presheaf to a sheaf extends by amalgamating the two successive matching families. -/
private def sheafificationHomInv (h : GluingLaws X)
    (P : (Over X)ᵒᵖ ⥤ Type u) (F : Sheaf (overFppfTopology X) (Type u))
    (α : P ⟶ F.obj) : sheafification.obj P ⟶ F :=
  ObjectProperty.homMk (plusLift h F (plusLift h F α))

/-- Restriction along the twofold matching-family unit gives the forward adjunction map. -/
private def sheafificationHomTo (P : (Over X)ᵒᵖ ⥤ Type u)
    (F : Sheaf (overFppfTopology X) (Type u)) (α : sheafification.obj P ⟶ F) : P ⟶ F.obj :=
  sheafificationUnit P ≫ α.hom

/-- Two successive unique amalgamations give the natural Hom equivalence of sheafification. -/
theorem sheafification_adjunction_laws :
    GluingLaws X ∧ ∀ h : GluingLaws X,
    (∀ (P : (Over X)ᵒᵖ ⥤ Type u) (F : Sheaf (overFppfTopology X) (Type u)),
      Function.LeftInverse (sheafificationHomInv h P F) (sheafificationHomTo P F) ∧
      Function.RightInverse (sheafificationHomInv h P F) (sheafificationHomTo P F)) ∧
    (∀ {P Q : (Over X)ᵒᵖ ⥤ Type u} {F : Sheaf (overFppfTopology X) (Type u)}
      (α : P ⟶ Q) (β : Q ⟶ F.obj),
      sheafificationHomInv h P F (α ≫ β) =
        sheafification.map α ≫ sheafificationHomInv h Q F β) ∧
    (∀ {P : (Over X)ᵒᵖ ⥤ Type u} {F G : Sheaf (overFppfTopology X) (Type u)}
      (α : sheafification.obj P ⟶ F) (β : F ⟶ G),
      sheafificationHomTo P G (α ≫ β) = sheafificationHomTo P F α ≫ β.hom) := by
  sorry

/-- The adjunction uses the explicit unit and successive unique amalgamations. -/
def sheafificationAdjunction : sheafification (X := X) ⊣ sheafToPresheaf (overFppfTopology X) (Type u) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P F ↦
        { toFun := sheafificationHomTo P F
          invFun := sheafificationHomInv (sheafification_adjunction_laws (X := X)).1 P F
          left_inv := (((sheafification_adjunction_laws (X := X)).2
            (sheafification_adjunction_laws (X := X)).1).1 P F).1
          right_inv := (((sheafification_adjunction_laws (X := X)).2
            (sheafification_adjunction_laws (X := X)).1).1 P F).2 }
      homEquiv_naturality_left_symm := ((sheafification_adjunction_laws (X := X)).2
        (sheafification_adjunction_laws (X := X)).1).2.1
      homEquiv_naturality_right := ((sheafification_adjunction_laws (X := X)).2
        (sheafification_adjunction_laws (X := X)).1).2.2 }

/-- The twofold matching-family sheafification preserves finite limits. -/
theorem sheafification_preservesFiniteLimits :
    PreservesFiniteLimits (sheafification (X := X)) := by
  sorry

/-- The small étale chart family, viewed in the big slice. -/
private def chartInclusion (X : AlgebraicSpace S) : SmallEtale.AtlasCharts.Site X ⥤ Over X :=
  SpacesEtale.AtlasCharts.inclusion X ⋙ Etale.SmallToBig.spacesEtaleToBig X

/-- A left-extension generator records a chart, an actual small-model arrow to it, and a section. -/
private def ChartGenerator (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u) (V : Over X) : Type u :=
  Σ c : SmallEtale.AtlasCharts.Site X,
    Shrink.{u} (V ⟶ (chartInclusion X).obj c) ×
      P.obj (op ((SpacesEtale.AtlasCharts.inclusion X).obj c))

/-- The coend relation identifies restriction of a section with postcomposition of its chart arrow. -/
private def chartRelation (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u) (V : Over X)
    (s t : ChartGenerator P V) : Prop :=
  ∃ (c d : SmallEtale.AtlasCharts.Site X) (h : c ⟶ d)
    (f : V ⟶ (chartInclusion X).obj c)
    (x : P.obj (op ((SpacesEtale.AtlasCharts.inclusion X).obj d))),
    s = ⟨c, (equivShrink _ f, P.map ((SpacesEtale.AtlasCharts.inclusion X).map h).op x)⟩ ∧
    t = ⟨d, (equivShrink _ (f ≫ (chartInclusion X).map h), x)⟩

/-- The left-extension section carrier is the small quotient by the contravariant coend relation. -/
private def chartExtensionValue (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u) (V : Over X) : Type u :=
  Quot (chartRelation P V)

/-- Restriction of a left-extension generator precomposes its actual chart arrow. -/
private def chartGeneratorRestriction (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u)
    {V W : Over X} (f : V ⟶ W) (s : ChartGenerator P W) : ChartGenerator P V :=
  ⟨s.1, (equivShrink _ (f ≫ (equivShrink _).symm s.2.1), s.2.2)⟩

/-- Restriction in the small coend is induced by precomposition on its generators. -/
private def chartExtensionRestriction (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u)
    {V W : Over X} (f : V ⟶ W) : chartExtensionValue P W → chartExtensionValue P V :=
  Quot.map (chartGeneratorRestriction P f) (by
    rintro s t ⟨c, d, h, g, x, rfl, rfl⟩
    refine ⟨c, d, h, f ≫ g, x, ?_, ?_⟩
    · simp only [chartGeneratorRestriction, Equiv.symm_apply_apply]
    · simp only [chartGeneratorRestriction, Equiv.symm_apply_apply, Category.assoc])

/-- The coend extension is a presheaf; its laws follow from composition of actual chart arrows. -/
private def chartExtensionObj (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u) : (Over X)ᵒᵖ ⥤ Type u where
  obj V := chartExtensionValue P V.unop
  map f := ↾(chartExtensionRestriction P f.unop)
  map_id V := by
    ext x
    refine Quot.inductionOn x ?_
    intro s
    change Quot.mk _ (chartGeneratorRestriction P (𝟙 V).unop s) = Quot.mk _ s
    congr 1
    cases s with
    | mk c s =>
      rcases s with ⟨g, x⟩
      simp only [chartGeneratorRestriction, unop_id, Category.id_comp, Equiv.apply_symm_apply]
  map_comp f g := by
    ext x
    refine Quot.inductionOn x ?_
    intro s
    change Quot.mk _ (chartGeneratorRestriction P (g.unop ≫ f.unop) s) =
      Quot.mk _ (chartGeneratorRestriction P g.unop (chartGeneratorRestriction P f.unop s))
    congr 1
    rcases s with ⟨c, g, x⟩
    dsimp [chartGeneratorRestriction]
    simp only [Equiv.symm_apply_apply, Category.assoc]

/-- A map of presheaves acts on coend generators by its section maps. -/
private def chartGeneratorMap {P Q : (spacesEtaleSite X)ᵒᵖ ⥤ Type u} (α : P ⟶ Q)
    (V : Over X) (s : ChartGenerator P V) : ChartGenerator Q V :=
  ⟨s.1, s.2.1, α.app _ s.2.2⟩

/-- The coend map is the quotient of the componentwise map of generators. -/
private def chartExtensionMap {P Q : (spacesEtaleSite X)ᵒᵖ ⥤ Type u} (α : P ⟶ Q) :
    chartExtensionObj P ⟶ chartExtensionObj Q where
  app V := ↾(Quot.map (chartGeneratorMap α V.unop) (by
    rintro s t ⟨c, d, h, f, x, rfl, rfl⟩
    refine ⟨c, d, h, f, α.app _ x, ?_, rfl⟩
    dsimp [chartGeneratorMap]
    congr 2
    exact ConcreteCategory.congr_hom (α.naturality
      ((SpacesEtale.AtlasCharts.inclusion X).map h).op) x))
  naturality {V W} f := by
    ext x
    refine Quot.inductionOn x ?_
    intro s
    rfl

/-- The small-chart coend extends presheaves from the étale site to the big slice. -/
private def chartExtension : ((spacesEtaleSite X)ᵒᵖ ⥤ Type u) ⥤ ((Over X)ᵒᵖ ⥤ Type u) where
  obj := chartExtensionObj
  map := chartExtensionMap
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
private def chartUnit (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u) :
    (SpacesEtale.AtlasCharts.inclusion X).op ⋙ P ⟶
      (chartInclusion X).op ⋙ chartExtensionObj P where
  app c := ↾fun x ↦ Quot.mk _ ⟨c.unop, equivShrink _ (𝟙 _), x⟩
  naturality {c d} h := by
    ext x
    apply Quot.sound
    refine ⟨d.unop, c.unop, h.unop, 𝟙 _, x, rfl, ?_⟩
    dsimp [chartExtensionObj, chartExtensionRestriction, chartGeneratorRestriction]
    simp only [Equiv.symm_apply_apply]
    change (⟨c.unop, equivShrink _ ((chartInclusion X).map h.unop ≫ 𝟙 _), x⟩ :
      ChartGenerator P _) = ⟨c.unop, equivShrink _ (𝟙 _ ≫ (chartInclusion X).map h.unop), x⟩
    simp only [Category.comp_id, Category.id_comp]

/-- A map into a restricted presheaf evaluates each generator by its chart arrow. -/
private def chartHomInv {P : (spacesEtaleSite X)ᵒᵖ ⥤ Type u}
    {Q : (Over X)ᵒᵖ ⥤ Type u}
    (α : P ⟶ (Etale.SmallToBig.spacesEtaleToBig X).op ⋙ Q) :
    chartExtensionObj P ⟶ Q where
  app V := ↾(Quot.lift (fun s : ChartGenerator P V.unop ↦
    Q.map ((equivShrink _).symm s.2.1).op (α.app _ s.2.2)) (by
      rintro s t ⟨c, d, h, f, x, rfl, rfl⟩
      simp only [Equiv.symm_apply_apply, op_comp, Functor.map_comp]
      have e := ConcreteCategory.congr_hom
        (α.naturality ((SpacesEtale.AtlasCharts.inclusion X).map h).op) x
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
def spacesPushforward (X : AlgebraicSpace S) :
    Sheaf (overFppfTopology X) (Type u) ⥤ Sheaf (spacesEtaleTopology X) (Type u) :=
  (Etale.SmallToBig.spacesEtaleToBig X).sheafPushforwardContinuous (Type u)
    (spacesEtaleTopology X) (overFppfTopology X)

/-- The comparison inverse image is the small-chart coend followed by twofold Plus. -/
def spacesInverseImage (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type u) ⥤ Sheaf (overFppfTopology X) (Type u) :=
  sheafToPresheaf (spacesEtaleTopology X) (Type u) ⋙ chartExtension ⋙ sheafification

/-- The forward adjunction map restricts to charts and then extends uniquely through the dense family. -/
private def comparisonHomTo (P : Sheaf (spacesEtaleTopology X) (Type u))
    (F : Sheaf (overFppfTopology X) (Type u))
    (α : (spacesInverseImage X).obj P ⟶ F) : P ⟶ (spacesPushforward X).obj F :=
  ObjectProperty.homMk
    (Functor.IsCoverDense.restrictHomEquivHom
      (G := SpacesEtale.AtlasCharts.inclusion X)
      (ℱ' := (spacesPushforward X).obj F)
      (chartUnit P.obj ≫ Functor.whiskerLeft (chartInclusion X).op
        ((sheafificationAdjunction (X := X)).homEquiv _ _ α)))

/-- The reverse adjunction map evaluates coend generators and amalgamates twice. -/
private def comparisonHomInv (P : Sheaf (spacesEtaleTopology X) (Type u))
    (F : Sheaf (overFppfTopology X) (Type u))
    (α : P ⟶ (spacesPushforward X).obj F) : (spacesInverseImage X).obj P ⟶ F :=
  ((sheafificationAdjunction (X := X)).homEquiv _ _).symm (chartHomInv α.hom)

/-- Chart evaluation and twofold amalgamation are inverse natural hom correspondences. -/
theorem comparison_adjunction_laws :
    (∀ (P : Sheaf (spacesEtaleTopology X) (Type u))
      (F : Sheaf (overFppfTopology X) (Type u)),
      (∀ α, comparisonHomInv P F (comparisonHomTo P F α) = α) ∧
      (∀ α, comparisonHomTo P F (comparisonHomInv P F α) = α)) ∧
    (∀ {P Q : Sheaf (spacesEtaleTopology X) (Type u)} (α : P ⟶ Q)
      {F : Sheaf (overFppfTopology X) (Type u)} (β : Q ⟶ (spacesPushforward X).obj F),
      comparisonHomInv P F (α ≫ β) =
        (spacesInverseImage X).map α ≫ comparisonHomInv Q F β) ∧
    (∀ {P : Sheaf (spacesEtaleTopology X) (Type u)}
      {F G : Sheaf (overFppfTopology X) (Type u)}
      (α : (spacesInverseImage X).obj P ⟶ F) (β : F ⟶ G),
      comparisonHomTo P G (α ≫ β) =
        comparisonHomTo P F α ≫ (spacesPushforward X).map β) := by
  sorry

/-- The small-chart comparison inverse image preserves finite limits. -/
theorem comparison_preservesFiniteLimits (X : AlgebraicSpace S) :
    PreservesFiniteLimits (spacesInverseImage X) := by
  sorry

/-- The fppf-to-étale comparison is defined with small coefficients and explicit chartwise inverse image. -/
def spacesComparison (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (spacesEtaleTopology X) (overFppfTopology X) where
  inverseImageFunctor := ⟨spacesInverseImage X, comparison_preservesFiniteLimits X⟩
  pushforward := spacesPushforward X
  adjunction := Adjunction.mkOfHomEquiv
    { homEquiv := fun P F ↦
        { toFun := comparisonHomTo P F
          invFun := comparisonHomInv P F
          left_inv := ((comparison_adjunction_laws (X := X)).1 P F).1
          right_inv := ((comparison_adjunction_laws (X := X)).1 P F).2 }
      homEquiv_naturality_left_symm := fun f g ↦ (comparison_adjunction_laws (X := X)).2.1 f g
      homEquiv_naturality_right := fun f g ↦ (comparison_adjunction_laws (X := X)).2.2 f g }

end AlgebraicGeometry.AlgebraicSpace.Fppf.SmallCoefficients
