/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cofiltered.ColimitPullback

/-!
# Explicit sections on a cofiltered colimit site

For a sheaf on one stage of a cofiltered site diagram, this module gives an
explicit quotient model for sections on the colimit site.  A section is first
represented at a lower stage and then identified with another representative
when both lower to the same section.  The resulting quotient is functorial in
the colimit category and defines the auxiliary sheaf used in filtered-colimit
arguments.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

noncomputable section

namespace CategoryTheory.CofilteredSiteDiagram.ColimitSection

variable (S : CofilteredSiteDiagram.{u, u, u})

/-- The adjoint-transpose map which lowers a section of the pullback along
`a : j ⟶ i` further along `b : k ⟶ j`. -/
noncomputable def lowerMap {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    (ColimitPullback.stagePullback S a).obj F ⟶
      ((S.stageFunctor b).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) (S.stageTopology k)).obj
        ((ColimitPullback.stagePullback S (b ≫ a)).obj F) :=
  (((S.stageFunctor b).sheafAdjunctionContinuous (Type u)
    (S.stageTopology j) (S.stageTopology k)).homEquiv _ _)
    ((S.stageSheafPullbackCompIso (Type u) a b).hom.app F)

/-- A concrete stage representative of a section over an object of the
cofiltered colimit category. -/
structure Representative {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    (V : S.ColimitCategory) where
  /-- The stage presenting the section. -/
  stage : S.I
  /-- The arrow from the presenting stage to the base stage of `F`. -/
  toBase : stage ⟶ i
  /-- The presenting object at that stage. -/
  obj : S.stage stage
  /-- The equality between the presented colimit object and `V`. -/
  eqToColimit : S.ιObj stage obj = V
  /-- The section of the pulled-back sheaf at the presenting object. -/
  value : ((ColimitPullback.stagePullback S toBase).obj F).obj.obj (op obj)

/-- The section obtained by lowering a representative along one index arrow. -/
noncomputable def Representative.lowerSection
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    (r : Representative S F V) {k : S.I} (b : k ⟶ r.stage) :
  ((ColimitPullback.stagePullback S (b ≫ r.toBase)).obj F).obj.obj
      (op ((S.stageFunctor b).obj r.obj)) :=
  ((lowerMap S F r.toBase b).1.app (op r.obj)) r.value

/-- Lower a representative along an arrow of the cofiltered indexing category. -/
noncomputable def Representative.lower
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    (r : Representative S F V) {k : S.I} (b : k ⟶ r.stage) : Representative S F V where
  stage := k
  toBase := b ≫ r.toBase
  obj := (S.stageFunctor b).obj r.obj
  eqToColimit := (S.ιObj_lower b r.obj).trans r.eqToColimit
  value := r.lowerSection b

/-- The section field of a lowered representative is its lowering map applied
to the original section. -/
theorem Representative.lower_section
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    (r : Representative S F V) {k : S.I} (b : k ⟶ r.stage) :
    (r.lower b).value = r.lowerSection b := sorry

/-- The section types agree after equalizing both the stage arrow and the
presenting stage object. -/
theorem sectionTypeCongr {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {k : S.I} {a a' : k ⟶ i} (ha : a = a') {W W' : S.stage k} (hW : W = W') :
    ((ColimitPullback.stagePullback S a).obj F).obj.obj (op W) =
      ((ColimitPullback.stagePullback S a').obj F).obj.obj (op W') := sorry

/-- Two representatives are related when common lowerings have the same
base-stage arrow, object, and section. -/
def Representative.Rel
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    (r₁ r₂ : Representative S F V) : Prop :=
  ∃ (k : S.I) (b₁ : k ⟶ r₁.stage) (b₂ : k ⟶ r₂.stage)
    (hBase : b₁ ≫ r₁.toBase = b₂ ≫ r₂.toBase)
    (hObj : (S.stageFunctor b₁).obj r₁.obj = (S.stageFunctor b₂).obj r₂.obj),
    eqToHom (sectionTypeCongr S F hBase hObj) (r₁.lower b₁).value =
      (r₂.lower b₂).value

/-- Common lowering relates every representative to itself. -/
theorem Representative.rel_refl
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    (r : Representative S F V) : r.Rel r := sorry

/-- The common-lowering relation is symmetric. -/
theorem Representative.rel_symm
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    {r₁ r₂ : Representative S F V} (h : r₁.Rel r₂) : r₂.Rel r₁ := sorry

/-- The common-lowering relation is transitive. -/
theorem Representative.rel_trans
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    {r₁ r₂ r₃ : Representative S F V} (h₁₂ : r₁.Rel r₂) (h₂₃ : r₂.Rel r₃) :
    r₁.Rel r₃ := sorry

/-- The setoid on representatives generated by equality after common
lowering. -/
def Representative.setoid {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    (V : S.ColimitCategory) : Setoid (Representative S F V) where
  r := Representative.Rel (S := S)
  iseqv := ⟨Representative.rel_refl, Representative.rel_symm, Representative.rel_trans⟩

/-- The quotient of stage section representatives by common lowering. -/
def Section {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) (V : S.ColimitCategory) :
    Type u :=
  _root_.Quotient (Representative.setoid S F V)

/-- The class of one concrete section representative. -/
def Section.mk {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    (r : Representative S F V) : Section S F V :=
  _root_.Quotient.mk (Representative.setoid S F V) r

/-- Every quotient section has a representative. -/
theorem Section.mk_surjective
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    (s : Section S F V) : ∃ r : Representative S F V, Section.mk r = s := sorry

/-- Equality of quotient classes is exactly the common-lowering relation. -/
theorem Section.mk_eq_mk
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    {r₁ r₂ : Representative S F V} :
    Section.mk r₁ = Section.mk r₂ ↔ r₁.Rel r₂ := sorry

/-- A representative and each of its lowerings determine the same quotient
section. -/
theorem Representative.mk_lower_eq
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)} {V : S.ColimitCategory}
    (r : Representative S F V) {k : S.I} (b : k ⟶ r.stage) :
    Section.mk (r.lower b) = Section.mk r := sorry

/-- Data which presents the action of a colimit-category morphism on a section
representative at one common lower stage. -/
structure RestrictionData {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {x y : S.ColimitCategory} (g : S.HomRep x y) (r : Representative S F y) where
  /-- The common lowering stage. -/
  stage : S.I
  /-- The lowering arrow for the morphism representative. -/
  toMorphism : stage ⟶ g.idx
  /-- The lowering arrow for the section representative. -/
  toRepresentative : stage ⟶ r.stage
  /-- The identification of the lowered target objects. -/
  glue : (S.stageFunctor toMorphism).obj g.tgt =
    (S.stageFunctor toRepresentative).obj r.obj

/-- A canonical choice of restriction data, extracted directly from equality
of the two colimit-object presentations. -/
noncomputable def RestrictionData.some
    {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {x y : S.ColimitCategory} (g : S.HomRep x y) (r : Representative S F y) :
    RestrictionData S F g r :=
  let h : S.objRel ⟨g.idx, g.tgt⟩ ⟨r.stage, r.obj⟩ :=
    _root_.Quotient.exact (g.htgt.trans r.eqToColimit.symm)
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec⟩

/-- The defining common-lowering equality of `RestrictionData.some`. -/
theorem RestrictionData.some_spec
    {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {x y : S.ColimitCategory} (g : S.HomRep x y) (r : Representative S F y) :
    (S.stageFunctor (RestrictionData.some S F g r).toMorphism).obj g.tgt =
      (S.stageFunctor (RestrictionData.some S F g r).toRepresentative).obj r.obj := sorry

/-- Restrict a representative along a concrete morphism representative using
chosen common-lowering data. -/
noncomputable def RestrictionData.restrict
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)}
    {x y : S.ColimitCategory} {g : S.HomRep x y} {r : Representative S F y}
    (d : RestrictionData S F g r) : Representative S F x where
  stage := d.stage
  toBase := d.toRepresentative ≫ r.toBase
  obj := (S.stageFunctor d.toMorphism).obj g.src
  eqToColimit := (S.ιObj_lower d.toMorphism g.src).trans g.hsrc
  value :=
    (((ColimitPullback.stagePullback S (d.toRepresentative ≫ r.toBase)).obj F).obj.map
      ((S.stageFunctor d.toMorphism).map g.hom ≫ eqToHom d.glue).op)
      ((r.lower d.toRepresentative).value)

/-- Restriction of representatives respects both morphism and section
common-lowering relations. -/
theorem RestrictionData.restrict_sound
    {S : CofilteredSiteDiagram.{u, u, u}} {i : S.I}
    {F : Sheaf (S.stageTopology i) (Type u)}
    {x y : S.ColimitCategory} {g₁ g₂ : S.HomRep x y}
    {r₁ r₂ : Representative S F y} (hg : S.homRel g₁ g₂) (hr : r₁.Rel r₂)
    (d₁ : RestrictionData S F g₁ r₁) (d₂ : RestrictionData S F g₂ r₂) :
    (d₁.restrict).Rel d₂.restrict := sorry

/-- Restrict a quotient section along a morphism of the colimit category. -/
noncomputable def restrict {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {x y : S.ColimitCategory} (f : x ⟶ y) (s : Section S F y) : Section S F x :=
  _root_.Quotient.lift₂
    (fun (g : S.HomRep x y) (r : Representative S F y) =>
      Section.mk ((RestrictionData.some S F g r).restrict))
    (fun _ _ _ _ hg hr => _root_.Quotient.sound
      (RestrictionData.restrict_sound hg hr
        (RestrictionData.some S F _ _) (RestrictionData.some S F _ _)))
    f s

/-- The quotient restriction map is computed by any choice of restriction
data on representative classes. -/
theorem restrict_mk_mk {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {x y : S.ColimitCategory} (g : S.HomRep x y) (r : Representative S F y)
    (d : RestrictionData S F g r) :
    restrict S F (_root_.Quotient.mk _ g : x ⟶ y) (Section.mk r) =
      Section.mk d.restrict := sorry

/-- Restriction along an identity morphism is the identity on quotient
sections. -/
theorem restrict_id {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {y : S.ColimitCategory} (s : Section S F y) :
    restrict S F (𝟙 y) s = s := sorry

/-- Restriction along a composite is the composite of quotient restrictions. -/
theorem restrict_comp {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {x y z : S.ColimitCategory} (f : x ⟶ y) (g : y ⟶ z) (s : Section S F z) :
    restrict S F (f ≫ g) s = restrict S F f (restrict S F g s) := sorry

/-- The identity law needed for the quotient-section presheaf. -/
theorem presheaf_map_id {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    (V : S.ColimitCategoryᵒᵖ) :
    TypeCat.ofHom (fun s : Section S F V.unop => restrict S F (𝟙 V).unop s) =
      𝟙 (Section S F V.unop) := sorry

/-- The composition law needed for the quotient-section presheaf. -/
theorem presheaf_map_comp {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {V V' V'' : S.ColimitCategoryᵒᵖ} (f : V ⟶ V') (g : V' ⟶ V'') :
    TypeCat.ofHom (fun s : Section S F V.unop => restrict S F (f ≫ g).unop s) =
      TypeCat.ofHom (fun s => restrict S F f.unop s) ≫
        TypeCat.ofHom (fun s => restrict S F g.unop s) := sorry

/-- The presheaf on the colimit category represented by quotient sections. -/
noncomputable def presheaf {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) :
    S.ColimitCategoryᵒᵖ ⥤ Type u where
  obj V := Section S F V.unop
  map := fun f => TypeCat.ofHom (restrict S F f.unop)
  map_id := presheaf_map_id S F
  map_comp := presheaf_map_comp S F

/-- The quotient-section presheaf satisfies the sheaf condition for the
colimit topology. -/
theorem presheaf_isSheaf {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) :
    Presieve.IsSheaf S.colimitTopology (presheaf S F) := sorry

/-- The auxiliary sheaf on the colimit site built from quotient sections. -/
noncomputable def sheaf {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) :
    Sheaf S.colimitTopology (Type u) :=
  ⟨presheaf S F,
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).2 (presheaf_isSheaf S F)⟩

/-- The canonical map from a stage pullback to the pushforward of the
quotient-section sheaf along the corresponding colimit cocone functor. -/
noncomputable def stageMap {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {j : S.I} (a : j ⟶ i) :
    (ColimitPullback.stagePullback S a).obj F ⟶
      ((S.stageCoconeFunctor j).sheafPushforwardContinuous (Type u)
        (S.stageTopology j) S.colimitTopology).obj (sheaf S F) where
  hom :=
    { app := fun W => TypeCat.ofHom (fun s =>
        Section.mk
          ({ stage := j
             toBase := a
             obj := W.unop
             eqToColimit := rfl
             value := s } : Representative S F (S.ιObj j W.unop)))
      naturality := sorry }

/-- A stage-map component sends a section to its tautological representative
class. -/
theorem stageMap_app {i : S.I} (F : Sheaf (S.stageTopology i) (Type u))
    {j : S.I} (a : j ⟶ i) (W : (S.stage j)ᵒᵖ)
    (s : ((ColimitPullback.stagePullback S a).obj F).obj.obj W) :
    ((stageMap S F a).hom.app W) s =
      Section.mk
        ({ stage := j
           toBase := a
           obj := W.unop
           eqToColimit := rfl
           value := s } : Representative S F (S.ιObj j W.unop)) := sorry

/-- The identity-stage map from a sheaf to the pushforward of its
quotient-section sheaf. -/
noncomputable def unit {i : S.I} (F : Sheaf (S.stageTopology i) (Type u)) :
    F ⟶ ((S.stageCoconeFunctor i).sheafPushforwardContinuous (Type u)
      (S.stageTopology i) S.colimitTopology).obj (sheaf S F) :=
  ((S.stageSheafPullbackIdIso (Type u) i).inv.app F) ≫ stageMap S F (𝟙 i)

end CategoryTheory.CofilteredSiteDiagram.ColimitSection
