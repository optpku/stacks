/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Atlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets.Points

/-!
# Representing object of Isom on a quotient stack

This module constructs the algebraic space `S' ×_{(y', x')} R` representing morphisms in
`[U/_p R]` between two scheme-valued points of `U`, together with its relative sheaf of
points on `(Sch/S')_fppf` with restrictions given by precomposition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The algebraic space `S' ×_{(y', x'), U ×_S U} R` obtained by pulling `R → U ×_S U` back
along `(y', x') : S' → U ×_S U`. The pairing is `(t, s)`, so a point of `R` has target `y'` and source `x'`. -/
def isomPullback {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) : AlgebraicSpace S :=
  pullback (prod.lift y' x') (prod.lift G.t.left G.s.left)

/-- The structure morphism of `isomPullback G x' y'` to `S'` over `S`. -/
def isomPullback_fst {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    isomPullback G x' y' ⟶ ofOver S' :=
  pullback.fst (prod.lift y' x') (prod.lift G.t.left G.s.left)

/-- The projection of `isomPullback G x' y'` to the arrow space `R`. -/
def isomPullback_snd {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    isomPullback G x' y' ⟶ G.R.left :=
  pullback.snd (prod.lift y' x') (prod.lift G.t.left G.s.left)

/-- The two projections of `isomPullback G x' y'` agree in `U ×_S U`. -/
theorem isomPullback_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    isomPullback_fst G x' y' ≫ prod.lift y' x' =
      isomPullback_snd G x' y' ≫ prod.lift G.t.left G.s.left :=
  pullback.condition

/-- A morphism `T → R` over `S` is a `T`-point of `isomPullback G x' y'` over `S'` if and
only if it has target `T → S' → U` given by `y'` and source given by `x'`. -/
theorem mem_isomPullback_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T : Over S} (φ : T ⟶ S') (r : ofOver T ⟶ G.R.left) :
    (∃ f : ofOver T ⟶ isomPullback G x' y',
        f ≫ isomPullback_fst G x' y' = ofOverMap φ ∧
          f ≫ isomPullback_snd G x' y' = r) ↔
      r ≫ G.t.left = ofOverMap φ ≫ y' ∧ r ≫ G.s.left = ofOverMap φ ≫ x' :=
  by
    constructor
    · rintro ⟨f, hf, hr⟩
      have h : ofOverMap φ ≫ prod.lift y' x' =
          r ≫ prod.lift G.t.left G.s.left := by
        simpa only [← Category.assoc, hf, hr] using
          congrArg (fun k ↦ f ≫ k) (isomPullback_condition G x' y')
      constructor
      · simpa only [Category.assoc, prod.lift_fst] using
          (congrArg (fun k ↦ k ≫ prod.fst) h).symm
      · simpa only [Category.assoc, prod.lift_snd] using
          (congrArg (fun k ↦ k ≫ prod.snd) h).symm
    · rintro ⟨ht, hs⟩
      have h : ofOverMap φ ≫ prod.lift y' x' =
          r ≫ prod.lift G.t.left G.s.left := by
        apply prod.hom_ext
        · simpa only [Category.assoc, prod.lift_fst] using ht.symm
        · simpa only [Category.assoc, prod.lift_snd] using hs.symm
      exact ⟨pullback.lift (ofOverMap φ) r h,
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/-- A `T`-section of the relative points of `isomPullback G x' y'` over `S'`. -/
def isomPullbackSection {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    (T : (Over S')ᵒᵖ) : Type (u + 1) :=
  { r : ofOver T.unop.left ⟶ G.R.left //
    r ≫ G.t.left = ofOverMap T.unop.hom ≫ y' ∧
      r ≫ G.s.left = ofOverMap T.unop.hom ≫ x' }

/-- Precomposing a relative arrow with a morphism over the base preserves its endpoints. -/
theorem isomPullbackSection.restrict_endpoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T₁ T₂ : (Over S')ᵒᵖ} (φ : T₁ ⟶ T₂) (r : isomPullbackSection G x' y' T₁) :
    (ofOverMap φ.unop.left ≫ r.1) ≫ G.t.left = ofOverMap T₂.unop.hom ≫ y' ∧
      (ofOverMap φ.unop.left ≫ r.1) ≫ G.s.left = ofOverMap T₂.unop.hom ≫ x' :=
  by
    have hφ : ofOverMap φ.unop.left ≫ ofOverMap T₁.unop.hom =
        ofOverMap T₂.unop.hom := by
      change yoneda.map φ.unop.left ≫ yoneda.map T₁.unop.hom =
        yoneda.map T₂.unop.hom
      rw [← yoneda.map_comp, Over.w φ.unop]
    constructor
    · rw [Category.assoc, r.property.1, ← Category.assoc, hφ]
    · rw [Category.assoc, r.property.2, ← Category.assoc, hφ]

/-- Restrict a relative `R`-point along a morphism of schemes over `S'`. -/
def isomPullbackSection.restrict {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T₁ T₂ : (Over S')ᵒᵖ} (φ : T₁ ⟶ T₂) (r : isomPullbackSection G x' y' T₁) :
    isomPullbackSection G x' y' T₂ :=
  ⟨ofOverMap φ.unop.left ≫ r.1,
    isomPullbackSection.restrict_endpoints G x' y' φ r⟩

/-- Restriction of a relative `R`-point is precomposition with `ofOverMap`. -/
theorem isomPullbackSection.restrict_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T₁ T₂ : (Over S')ᵒᵖ} (φ : T₁ ⟶ T₂) (r : isomPullbackSection G x' y' T₁) :
    (isomPullbackSection.restrict G x' y' φ r).1 = ofOverMap φ.unop.left ≫ r.1 :=
  rfl

/-- Restricting a relative arrow along an identity leaves it unchanged. -/
theorem isomPullbackSection.restrict_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    (T : (Over S')ᵒᵖ) (r : isomPullbackSection G x' y' T) :
    isomPullbackSection.restrict G x' y' (𝟙 T) r = r :=
  by
    apply Subtype.ext
    change yoneda.map (𝟙 T.unop.left) ≫ r.1 = r.1
    rw [yoneda.map_id, Category.id_comp]

/-- Restricting a relative arrow along a composite equals successive restriction. -/
theorem isomPullbackSection.restrict_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T₁ T₂ T₃ : (Over S')ᵒᵖ} (φ : T₁ ⟶ T₂) (ψ : T₂ ⟶ T₃)
    (r : isomPullbackSection G x' y' T₁) :
    isomPullbackSection.restrict G x' y' (φ ≫ ψ) r =
      isomPullbackSection.restrict G x' y' ψ (isomPullbackSection.restrict G x' y' φ r) :=
  by
    apply Subtype.ext
    change yoneda.map (ψ.unop.left ≫ φ.unop.left) ≫ r.1 =
      yoneda.map ψ.unop.left ≫ (yoneda.map φ.unop.left ≫ r.1)
    rw [yoneda.map_comp, Category.assoc]

/-- The presheaf on `(Sch/S')_fppf` whose value at `T → S'` is the type of morphisms
`T → R` with target `T → S' → U` equal to `y'` and source equal to `x'`. -/
def isomPullbackPresheaf {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    (Over S')ᵒᵖ ⥤ Type (u + 1) where
  obj T := isomPullbackSection G x' y' T
  map φ := TypeCat.ofHom (isomPullbackSection.restrict G x' y' φ)
  map_id T := ConcreteCategory.hom_ext _ _
    (fun r ↦ isomPullbackSection.restrict_id G x' y' T r)
  map_comp φ ψ := ConcreteCategory.hom_ext _ _
    (fun r ↦ isomPullbackSection.restrict_comp G x' y' φ ψ r)

/-- Restriction of a section of `isomPullbackPresheaf` is precomposition with `ofOverMap`. -/
theorem isomPullbackPresheaf_map_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T₁ T₂ : (Over S')ᵒᵖ} (φ : T₁ ⟶ T₂) (r : (isomPullbackPresheaf G x' y').obj T₁) :
    ((isomPullbackPresheaf G x' y').map φ r).1 = ofOverMap φ.unop.left ≫ r.1 :=
  rfl

/-- The relative points presheaf of `isomPullback G x' y'` is an fppf sheaf on `Sch/S'`. -/
theorem isomPullbackPresheaf_isSheaf {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    Presheaf.IsSheaf ((Scheme.fppfTopology.over S).over S')
      (isomPullbackPresheaf G x' y') :=
  by
    let J := (Scheme.fppfTopology.over S).over S'
    let H (X : AlgebraicSpace S) : (Over S')ᵒᵖ ⥤ Type (u + 1) :=
      (Over.forget S' ⋙ ofOverFunctor S).op ⋙ yoneda.obj X
    have hH (X : AlgebraicSpace S) : Presieve.IsSheaf J (H X) := by
      let h := ((Scheme.fppfTopology.over S).overPullback (Type u) S').obj
        (⟨X.functorOfPoints, X.isSheaf⟩ : Sheaf (Scheme.fppfTopology.over S) (Type u))
      apply Presieve.isSheaf_of_nat_equiv
        (P₁ := h.obj) (fun {T} ↦ by
          change X.functorOfPoints.obj (op T.left) ≃
            (yoneda.obj T.left ⟶ X.functorOfPoints)
          exact yonedaEquiv.symm)
        (by
          intro V W f r
          change X.functorOfPoints.obj (op W.left) at r
          exact (yonedaEquiv_symm_naturality_left f.left X.functorOfPoints r).symm)
      exact (isSheaf_iff_isSheaf_of_type _ _).mp h.property
    let P : Subfunctor (H G.R.left) :=
      { obj := fun T ↦ { r | r ≫ G.t.left = ofOverMap T.unop.hom ≫ y' ∧
            r ≫ G.s.left = ofOverMap T.unop.hom ≫ x' }
        map := fun φ r hr ↦ isomPullbackSection.restrict_endpoints G x' y' φ ⟨r, hr⟩ }
    rw [isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf J P.toFunctor
    apply (P.isSheaf_iff (hH G.R.left)).mpr
    intro T r hr
    have hbase {V : Over S'} (f : V ⟶ T.unop) :
        ofOverMap f.left ≫ ofOverMap T.unop.hom = ofOverMap V.hom := by
      change yoneda.map f.left ≫ yoneda.map T.unop.hom = yoneda.map V.hom
      rw [← yoneda.map_comp, Over.w f]
    constructor
    · apply ((hH G.U.left) _ hr).isSeparatedFor.ext
      intro V f hf
      have ht : (ofOverMap f.left ≫ r) ≫ G.t.left = ofOverMap V.hom ≫ y' := hf.1
      change ofOverMap f.left ≫ (r ≫ G.t.left) =
        ofOverMap f.left ≫ (ofOverMap T.unop.hom ≫ y')
      simpa only [← Category.assoc, hbase f] using ht
    · apply ((hH G.U.left) _ hr).isSeparatedFor.ext
      intro V f hf
      have hs : (ofOverMap f.left ≫ r) ≫ G.s.left = ofOverMap V.hom ≫ x' := hf.2
      change ofOverMap f.left ≫ (r ≫ G.s.left) =
        ofOverMap f.left ≫ (ofOverMap T.unop.hom ≫ x')
      simpa only [← Category.assoc, hbase f] using hs

/-- The sheaf of `S'`-points of `S' ×_{(y', x'), U ×_S U} R` on `(Sch/S')_fppf`. -/
def isomPullbackSheaf {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    Sheaf ((Scheme.fppfTopology.over S).over S') (Type (u + 1)) :=
  ⟨isomPullbackPresheaf G x' y', isomPullbackPresheaf_isSheaf G x' y'⟩

/-- The underlying presheaf of `isomPullbackSheaf G x' y'` is `isomPullbackPresheaf G x' y'`. -/
theorem isomPullbackSheaf_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    (isomPullbackSheaf G x' y').obj = isomPullbackPresheaf G x' y' :=
  rfl

/-- A section of `isomPullbackSheaf G x' y'` over `T → S'` is an arrow of `R` with target
`y'` and source `x'` after restriction along `T → S'`. -/
theorem isomPullbackSheaf_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left)
    {T : Over S'} (s : (isomPullbackSheaf G x' y').obj.obj (op T)) :
    s.1 ≫ G.t.left = ofOverMap T.hom ≫ y' ∧
      s.1 ≫ G.s.left = ofOverMap T.hom ≫ x' :=
  s.property

/-- Before stackification, the Hom-presheaf of `[U/_p R]` between the images of `x'` and
`y'` is isomorphic to the sheaf of `S'`-points of `isomPullback G x' y'`. -/
theorem presheafHom_preQuotient_isIsomorphic_isomPullback
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    IsIsomorphic
      ((Functor.fiberPseudofunctor (preQuotient G).p).presheafHom
        (((atlasToPreQuotient G).fiberFunctor S').obj (objOfHom x'))
        (((atlasToPreQuotient G).fiberFunctor S').obj (objOfHom y')))
      (isomPullbackSheaf G x' y').obj :=
  sorry

/-- In the fppf quotient stack of a groupoid in algebraic spaces, the Hom sheaf between
two atlas images is isomorphic to the relative sheaf of arrows with those endpoints. -/
theorem sheafHom_atlas_isIsomorphic_isomPullback
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    IsIsomorphic
      ((Functor.fiberPseudofunctor (fppfQuotientStack G).p).sheafHom
        (Scheme.fppfTopology.over S)
        (((fppfAtlas G).fiberFunctor S').obj (objOfHom x'))
        (((fppfAtlas G).fiberFunctor S').obj (objOfHom y')))
      (isomPullbackSheaf G x' y') :=
  by
    obtain ⟨e⟩ := presheafHom_preQuotient_isIsomorphic_isomPullback G x' y'
    let J := (Scheme.fppfTopology.over S).over S'
    let a := ((atlasToPreQuotient G).fiberFunctor S').obj (objOfHom x')
    let b := ((atlasToPreQuotient G).fiberFunctor S').obj (objOfHom y')
    let F := (fppfQuotientStackPresentation G).comparison
    let P := (Functor.fiberPseudofunctor (preQuotient G).p).presheafHom a b
    let Q := (Functor.fiberPseudofunctor (fppfQuotientStack G).p).presheafHom
      ((F.fiberFunctor S').obj a) ((F.fiberFunctor S').obj b)
    let lP : P ⋙ uliftFunctor.{u + 1, u + 1} ≅ P :=
      Functor.isoWhiskerLeft P uliftFunctorTrivial ≪≫ P.rightUnitor
    let lQ : Q ⋙ uliftFunctor.{u + 1, u + 1} ≅ Q :=
      Functor.isoWhiskerLeft Q uliftFunctorTrivial ≪≫ Q.rightUnitor
    have hP : Presheaf.IsSheaf J P :=
      (Presheaf.isSheaf_of_iso_iff e).mpr (isomPullbackPresheaf_isSheaf G x' y')
    have hQ : Presheaf.IsSheaf J Q :=
      ((Functor.fiberPseudofunctor (fppfQuotientStack G).p).sheafHom
        (Scheme.fppfTopology.over S)
        ((F.fiberFunctor S').obj a) ((F.fiberFunctor S').obj b)).property
    let m := CartesianBasedFunctor.HomPresheaf.Chosen.map F a b
    have hm : J.W m :=
      (fppfQuotientStackPresentation G).isStackification.isLocalEquivalence.homPresheafMap_mem a b
    haveI : IsIso m :=
      (ObjectProperty.isLocal_iff_isIso _ _
        ((Presheaf.isSheaf_of_iso_iff lP).mpr hP)
        ((Presheaf.isSheaf_of_iso_iff lQ).mpr hQ)).mp hm
    exact ⟨ObjectProperty.isoMk _ (lQ.symm ≪≫ (asIso m).symm ≪≫ lP ≪≫ e)⟩

end AlgebraicGeometry.GroupoidAlgebraicSpace
