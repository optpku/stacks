/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap67.Lemma_67_4_13
public import stacks_project.Chap79.«79_12_0_2»
public import stacks_project.Chap79.Remark_79_12_5_Algebra

/-!
# Finite-part restriction of étale compactly supported 𝐅₂

For a separated locally quasi-finite morphism of schemes, compactly supported
sections of the constant 𝐅₂ sheaf on the small étale site compare with the
restriction of `(X/Y)_fin` along `Scheme.Etale.forget`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- The coefficient object of the constant 𝐅₂ sheaf, as `ULift (ZMod 2)`. -/
abbrev f2Coeff : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (ULift.{u} (ZMod 2))

/-- Unfolding `f2Coeff` recovers `AddCommGrpCat.of (ULift (ZMod 2))`. -/
theorem f2Coeff_eq : f2Coeff = AddCommGrpCat.of (ULift.{u} (ZMod 2)) :=
  sorry

/-- The constant étale sheaf of 𝐅₂ on a scheme. -/
abbrev constantF2 (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}] :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u} :=
  (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj f2Coeff

/-- Unfolding `constantF2` recovers the constant sheaf on `f2Coeff`. -/
theorem constantF2_obj (S : Scheme.{u})
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}] :
    constantF2 S =
      (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj f2Coeff :=
  sorry

/-- The sheafification unit of the constant 𝐅₂ presheaf at an étale object. -/
def constantF2ToSheafify {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}] (U : S.Etale) :
    f2Coeff ⟶ (constantF2 S).obj.obj (op U) :=
  (toSheafify S.smallEtaleTopology ((Functor.const S.Etaleᵒᵖ).obj f2Coeff)).app
    (op U)

/-- `constantF2ToSheafify` is the sheafification unit of the constant 𝐅₂
presheaf. -/
theorem constantF2ToSheafify_eq {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}] (U : S.Etale) :
    constantF2ToSheafify U =
      (toSheafify S.smallEtaleTopology
          ((Functor.const S.Etaleᵒᵖ).obj f2Coeff)).app (op U) :=
  sorry

/-- The morphism `Over.mk f ⟶ Over.mk (𝟙 Y)` associated to a scheme morphism
`f : X ⟶ Y`. -/
def ofSchemeHomOver {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Over.mk f ⟶ Over.mk (𝟙 Y) :=
  Over.homMk f (Category.comp_id f)

/-- `ofSchemeHomOver f` is `Over.homMk` of the identity triangle on `Y`. -/
theorem ofSchemeHomOver_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ofSchemeHomOver f = Over.homMk f (Category.comp_id f) :=
  sorry

/-- A scheme morphism `f : X ⟶ Y`, viewed as a morphism of algebraic spaces over
`Y`. -/
def ofSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ofOver (Over.mk f) ⟶ ofOver (Over.mk (𝟙 Y)) :=
  ofOverMap (ofSchemeHomOver f)

/-- `ofSchemeHom f` is `ofOverMap` of `ofSchemeHomOver f`. -/
theorem ofSchemeHom_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ofSchemeHom f = ofOverMap (ofSchemeHomOver f) :=
  sorry

/-- The underlying scheme morphism of `ofSchemeHomOver f` is `f`. -/
theorem ofSchemeHomOver_left {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ofSchemeHomOver f).left = f :=
  sorry

/-- Separatedness of a scheme morphism passes to `ofSchemeHom`. -/
instance instSeparated_ofSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsSeparated f] :
    AlgebraicSpace.Separated (ofSchemeHom f) :=
  sorry

/-- An étale `Y`-scheme, as a morphism of algebraic spaces over `Y`. -/
def etaleOverMap {Y : Scheme.{u}} (V : Y.Etale) :
    ofOver ((Scheme.Etale.forget Y).obj V) ⟶ ofOver (Over.mk (𝟙 Y)) :=
  ofOverMap (Over.homMk V.hom (Category.comp_id V.hom))

/-- `etaleOverMap V` is `ofOverMap` of the structure map `V ⟶ Y`. -/
theorem etaleOverMap_eq {Y : Scheme.{u}} (V : Y.Etale) :
    etaleOverMap V = ofOverMap (Over.homMk V.hom (Category.comp_id V.hom)) :=
  sorry

/-- A `T`-point of `ofOver U` determines the corresponding morphism `T ⟶ U` over the
base. -/
def ofOverPoint {Y : Scheme.{u}} {U : Over Y} {T : (Over Y)ᵒᵖ}
    (p : (ofOver U).functorOfPoints.obj T) : T.unop ⟶ U :=
  (yonedaEquiv.symm p).app (op T.unop) (𝟙 _)

/-- `ofOverPoint` evaluates the Yoneda inverse of a `T`-point at the identity of `T`. -/
theorem ofOverPoint_eq {Y : Scheme.{u}} {U : Over Y} {T : (Over Y)ᵒᵖ}
    (p : (ofOver U).functorOfPoints.obj T) :
    ofOverPoint p = (yonedaEquiv.symm p).app (op T.unop) (𝟙 _) :=
  sorry

/-- The identity `T`-point of `ofOver T`. -/
def ofOverIdPoint {Y : Scheme.{u}} (T : Over Y) :
    (ofOver T).functorOfPoints.obj (op T) :=
  yonedaEquiv (𝟙 (yoneda.obj T))

/-- `ofOverIdPoint T` is the Yoneda class of the identity of `yoneda.obj T`. -/
theorem ofOverIdPoint_eq {Y : Scheme.{u}} (T : Over Y) :
    ofOverIdPoint T = yonedaEquiv (𝟙 (yoneda.obj T)) :=
  sorry

/-- The restriction of `(X/Y)_fin` to the small étale site of `Y`. -/
def finitePartEtale {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology (Type u) :=
  ⟨(Scheme.Etale.forget Y).op ⋙ finitePart (ofSchemeHom f), sorry⟩

/-- Evaluating `finitePartEtale` at an étale `Y`-scheme recovers the shrunk
finite-part pairs over `V`. -/
theorem finitePartEtale_obj {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Etale) :
    (finitePartEtale f).obj.obj (op V) =
      Shrink (Point (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V)) :=
  sorry

/-- The underlying presheaf of `finitePartEtale` is the pullback of `finitePart`
along `Scheme.Etale.forget`. -/
theorem finitePartEtale_obj_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (finitePartEtale f).obj =
      (Scheme.Etale.forget Y).op ⋙ finitePart (ofSchemeHom f) :=
  sorry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/-- The scheme `V ×_Y X` as a scheme over `Y`. -/
def fiberAsOver (V : Y.Etale) : Over Y :=
  Over.mk (((smallEtalePullback f).obj V).hom ≫ f)

/-- The structure morphism of `fiberAsOver V` is the composite of the étale
pullback structure map with `f`. -/
theorem fiberAsOver_hom (V : Y.Etale) :
    (fiberAsOver f V).hom = ((smallEtalePullback f).obj V).hom ≫ f :=
  sorry

/-- The first projection `V ×_Y X ⟶ V` as a morphism of algebraic spaces over
`Y`. -/
def fiberFstOver (V : Y.Etale) :
    ofOver (fiberAsOver f V) ⟶ ofOver ((Scheme.Etale.forget Y).obj V) :=
  ofOverMap (Over.homMk (pullback.fst V.hom f) sorry)

/-- The second projection `V ×_Y X ⟶ X` as a morphism of algebraic spaces over
`Y`. -/
def fiberSndOver (V : Y.Etale) :
    ofOver (fiberAsOver f V) ⟶ ofOver (Over.mk f) :=
  ofOverMap (Over.homMk ((smallEtalePullback f).obj V).hom sorry)

/-- The comparison morphism from the scheme fibre `V ×_Y X` to the algebraic-space
pullback of `a` along `ofSchemeHom f`. -/
def fiberComparisonHom (V : Y.Etale)
    (a : ofOver ((Scheme.Etale.forget Y).obj V) ⟶ ofOver (Over.mk (𝟙 Y))) :
    ofOver (fiberAsOver f V) ⟶ pullback a (ofSchemeHom f) :=
  pullback.lift (fiberFstOver f V) (fiberSndOver f V) sorry

/-- `fiberComparisonHom` recovers the first projection of the algebraic-space pullback. -/
theorem fiberComparisonHom_fst (V : Y.Etale)
    (a : ofOver ((Scheme.Etale.forget Y).obj V) ⟶ ofOver (Over.mk (𝟙 Y))) :
    fiberComparisonHom f V a ≫ pullback.fst a (ofSchemeHom f) = fiberFstOver f V :=
  sorry

/-- The scheme morphism over `Y` associated to a `T`-point of the algebraic-space
pullback of `etaleOverMap V` along `ofSchemeHom f`. -/
def fiberComparisonInvOverHom (V : Y.Etale) {T : (Over Y)ᵒᵖ}
    (p : (pullback (etaleOverMap V) (ofSchemeHom f)).functorOfPoints.obj T) :
    T.unop ⟶ fiberAsOver f V :=
  Over.homMk
    (pullback.lift
      (ofOverPoint ((pullback.fst (etaleOverMap V) (ofSchemeHom f)).app T p)).left
      (ofOverPoint ((pullback.snd (etaleOverMap V) (ofSchemeHom f)).app T p)).left
      sorry)
    sorry

/-- `fiberComparisonInvOverHom` is a morphism of schemes over `Y`. -/
theorem fiberComparisonInvOverHom_w (V : Y.Etale) {T : (Over Y)ᵒᵖ}
    (p : (pullback (etaleOverMap V) (ofSchemeHom f)).functorOfPoints.obj T) :
    (fiberComparisonInvOverHom f V p).left ≫ (fiberAsOver f V).hom = (T.unop).hom :=
  sorry

/-- The inverse comparison from the algebraic-space pullback of `etaleOverMap V` along
`ofSchemeHom f` to the scheme fibre `V ×_Y X`. -/
def fiberComparisonInv (V : Y.Etale) :
    pullback (etaleOverMap V) (ofSchemeHom f) ⟶ ofOver (fiberAsOver f V) where
  app T := ↾fun p ↦
    (ofOverMap (fiberComparisonInvOverHom f V p)).app T (ofOverIdPoint T.unop)
  naturality := sorry

/-- Components of `fiberComparisonInv` are `ofOverMap` of `fiberComparisonInvOverHom`
evaluated at the identity point. -/
theorem fiberComparisonInv_app (V : Y.Etale) {T : (Over Y)ᵒᵖ}
    (p : (pullback (etaleOverMap V) (ofSchemeHom f)).functorOfPoints.obj T) :
    (fiberComparisonInv f V).app T p =
      (ofOverMap (fiberComparisonInvOverHom f V p)).app T (ofOverIdPoint T.unop) :=
  sorry

/-- The scheme fibre `V ×_Y X` is isomorphic to the algebraic-space pullback of
`etaleOverMap V` along `ofSchemeHom f`. -/
def fiberComparisonIso (V : Y.Etale) :
    ofOver (fiberAsOver f V) ≅ pullback (etaleOverMap V) (ofSchemeHom f) where
  hom := fiberComparisonHom f V (etaleOverMap V)
  inv := fiberComparisonInv f V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `fiberComparisonIso` is `fiberComparisonHom` of `etaleOverMap V`. -/
theorem fiberComparisonIso_hom (V : Y.Etale) :
    (fiberComparisonIso f V).hom = fiberComparisonHom f V (etaleOverMap V) :=
  sorry

/-- The inverse map of `fiberComparisonIso` is `fiberComparisonInv`. -/
theorem fiberComparisonIso_inv (V : Y.Etale) :
    (fiberComparisonIso f V).inv = fiberComparisonInv f V :=
  sorry

/-- The underlying type equivalence of the fibre comparison, as scheme points versus
algebraic-space pullback points. -/
def fiberComparisonPointsEquiv (V : Y.Etale) :
    (fiberAsOver f V).left ≃ Points (pullback (etaleOverMap V) (ofSchemeHom f)) :=
  (ofOver.pointsEquiv (fiberAsOver f V)).trans
    { toFun := Points.map (fiberComparisonIso f V).hom
      invFun := Points.map (fiberComparisonIso f V).inv
      left_inv := sorry
      right_inv := sorry }

/-- `fiberComparisonPointsEquiv` sends a scheme point to its image under
`fiberComparisonIso`. -/
theorem fiberComparisonPointsEquiv_apply (V : Y.Etale)
    (x : (fiberAsOver f V).left) :
    fiberComparisonPointsEquiv f V x =
      Points.map (fiberComparisonIso f V).hom
        (ofOver.pointsEquiv (fiberAsOver f V) x) :=
  sorry

/-- The fibre comparison as a homeomorphism from `|V ×_Y X|` to the points of
the algebraic-space pullback. -/
def fiberComparisonPointsHomeomorph (V : Y.Etale) :
    (fiberAsOver f V).left ≃ₜ Points (pullback (etaleOverMap V) (ofSchemeHom f)) :=
  Homeomorph.mk (fiberComparisonPointsEquiv f V) sorry sorry

/-- The underlying equivalence of `fiberComparisonPointsHomeomorph` is
`fiberComparisonPointsEquiv`. -/
theorem fiberComparisonPointsHomeomorph_toEquiv (V : Y.Etale) :
    (fiberComparisonPointsHomeomorph f V).toEquiv =
      fiberComparisonPointsEquiv f V :=
  sorry

/-- The map on points from the scheme fibre `|V ×_Y X|` to the algebraic-space
fibre of `a`. -/
def etaleFiberPointsMap (V : Y.Etale)
    (a : ofOver ((Scheme.Etale.forget Y).obj V) ⟶ ofOver (Over.mk (𝟙 Y))) :
    (fiberAsOver f V).left → Points (pullback a (ofSchemeHom f)) :=
  Points.mapOfOver (fiberComparisonHom f V a)

/-- `etaleFiberPointsMap` is `Points.mapOfOver` of `fiberComparisonHom`. -/
theorem etaleFiberPointsMap_eq (V : Y.Etale)
    (a : ofOver ((Scheme.Etale.forget Y).obj V) ⟶ ofOver (Over.mk (𝟙 Y))) :
    etaleFiberPointsMap f V a = Points.mapOfOver (fiberComparisonHom f V a) :=
  sorry

/-- On the structure map `etaleOverMap V`, the points map agrees with the fibre
comparison homeomorphism. -/
theorem etaleFiberPointsMap_eq_homeomorph (V : Y.Etale)
    (x : (fiberAsOver f V).left) :
    etaleFiberPointsMap f V (etaleOverMap V) x =
      fiberComparisonPointsHomeomorph f V x :=
  sorry

/-- The closed étale support of a compactly supported 𝐅₂-section, as a set in
the scheme fibre. -/
def sectionSupportSet (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) : Set (fiberAsOver f V).left :=
  (abelianSheafSectionSupport (constantF2 X) ((smallEtalePullback f).obj V)
      ((compactSupportSections f (constantF2 X) V).subtype σ)).carrier

/-- `sectionSupportSet` is the carrier of `abelianSheafSectionSupport`. -/
theorem sectionSupportSet_eq (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    sectionSupportSet f V σ =
      (abelianSheafSectionSupport (constantF2 X) ((smallEtalePullback f).obj V)
          ((compactSupportSections f (constantF2 X) V).subtype σ)).carrier :=
  sorry

/-- The support of a section of a constant abelian étale sheaf is open. -/
theorem isOpen_sectionSupport_constant (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    IsOpen (sectionSupportSet f V σ) :=
  sorry

/-- The closed étale support of a compactly supported 𝐅₂-section, as an open of
the scheme fibre. -/
def sectionSupportOpens (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    ((smallEtalePullback f).obj V).left.Opens :=
  ⟨sectionSupportSet f V σ, isOpen_sectionSupport_constant f V σ⟩

/-- The carrier of `sectionSupportOpens` is `sectionSupportSet`. -/
theorem sectionSupportOpens_carrier (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    (sectionSupportOpens f V σ).carrier = sectionSupportSet f V σ :=
  sorry

/-- The finite-part open `Z = Supp(s)` associated to a compactly supported 𝐅₂
section, obtained by transporting the étale support along the fibre comparison
homeomorphism. -/
def supportOpens (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    TopologicalSpace.Opens (Points (pullback (etaleOverMap V) (ofSchemeHom f))) :=
  ⟨fiberComparisonPointsHomeomorph f V '' sectionSupportSet f V σ, sorry⟩

/-- The carrier of `supportOpens` is the image of the étale section support along
the fibre comparison homeomorphism. -/
theorem supportOpens_carrier (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    (supportOpens f V σ).carrier =
      fiberComparisonPointsHomeomorph f V '' sectionSupportSet f V σ :=
  sorry

/-- `supportOpens` transports `abelianSheafSectionSupport` of the underlying
compactly supported section. -/
theorem supportOpens_eq_sectionSupport (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    (supportOpens f V σ).carrier =
      fiberComparisonPointsHomeomorph f V ''
        (abelianSheafSectionSupport (constantF2 X) ((smallEtalePullback f).obj V)
          ((compactSupportSections f (constantF2 X) V).subtype σ)).carrier :=
  sorry

/-- The finite-part pair `(V ⟶ Y, Supp(s))` attached to a compactly supported
𝐅₂-section. -/
def ofSection (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    Point (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V) where
  a := etaleOverMap V
  Z := supportOpens f V σ
  isFinite := sorry

/-- `ofSection` records the structure map `V ⟶ Y`. -/
theorem ofSection_a (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    (ofSection f V σ).a = etaleOverMap V :=
  sorry

/-- `ofSection` records the support open of the compactly supported section. -/
theorem ofSection_Z (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    (ofSection f V σ).Z = supportOpens f V σ :=
  sorry

/-- The scheme-side open underlying a finite-part pair, as the preimage of `Z`
along `etaleFiberPointsMap`. -/
def schemeSupportOpens (V : Y.Etale)
    (p : Point (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V)) :
    ((smallEtalePullback f).obj V).left.Opens :=
  ⟨etaleFiberPointsMap f V p.a ⁻¹' p.Z.carrier, sorry⟩

/-- The carrier of `schemeSupportOpens` is the preimage of `p.Z`. -/
theorem schemeSupportOpens_carrier (V : Y.Etale)
    (p : Point (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V)) :
    (schemeSupportOpens f V p).carrier =
      etaleFiberPointsMap f V p.a ⁻¹' p.Z.carrier :=
  sorry

/-- The clopen level set of the characteristic function of an open `Z ⊆ U`. -/
def supportLevelOpen {U : X.Etale} (Z : U.left.Opens) (hZ : IsClosed Z.carrier)
    (b : ZMod 2) : U.left.Opens :=
  if b = 1 then Z else ⟨Z.carrierᶜ, isOpen_compl_iff.mpr hZ⟩

/-- Membership in `supportLevelOpen` is the characteristic function of `Z`. -/
theorem mem_supportLevelOpen {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) (b : ZMod 2) (x : U.left) :
    x ∈ supportLevelOpen Z hZ b ↔ (x ∈ Z.carrier ↔ b = 1) :=
  sorry

/-- The étale `X`-scheme cut out by a characteristic level set. -/
def supportLevelEtale {U : X.Etale} (Z : U.left.Opens) (hZ : IsClosed Z.carrier)
    (b : ZMod 2) : X.Etale :=
  Scheme.Etale.mk ((supportLevelOpen Z hZ b).ι ≫ U.hom)

/-- The structure morphism of a characteristic level set is the open immersion
followed by `U.hom`. -/
theorem supportLevelEtale_hom {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) (b : ZMod 2) :
    (supportLevelEtale Z hZ b).hom = (supportLevelOpen Z hZ b).ι ≫ U.hom :=
  sorry

/-- The open immersion of a characteristic level set as a morphism of étale
`X`-schemes. -/
def supportLevelHom {U : X.Etale} (Z : U.left.Opens) (hZ : IsClosed Z.carrier)
    (b : ZMod 2) : supportLevelEtale Z hZ b ⟶ U :=
  MorphismProperty.Over.homMk (supportLevelOpen Z hZ b).ι sorry

/-- The underlying scheme morphism of `supportLevelHom` is the open immersion of
the level set. -/
theorem supportLevelHom_left {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) (b : ZMod 2) :
    (supportLevelHom Z hZ b).left = (supportLevelOpen Z hZ b).ι :=
  sorry

/-- The two characteristic level-set morphisms cover `U` in the small étale
topology. -/
theorem supportLevel_covers {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) :
    Sieve.ofArrows _ (supportLevelHom Z hZ) ∈ X.smallEtaleTopology U :=
  sorry

/-- Constant 𝐅₂-sections on characteristic level sets. -/
def supportLevelFamily {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) (b : ZMod 2) :
    f2Coeff ⟶ (constantF2 X).obj.obj (op (supportLevelEtale Z hZ b)) :=
  (if b = 1 then 𝟙 f2Coeff else 0) ≫
    constantF2ToSheafify (supportLevelEtale Z hZ b)

/-- The level-set family is the sheafification unit, scaled by the 𝐅₂-value. -/
theorem supportLevelFamily_eq {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) (b : ZMod 2) :
    supportLevelFamily Z hZ b =
      (if b = 1 then 𝟙 f2Coeff else 0) ≫
        constantF2ToSheafify (supportLevelEtale Z hZ b) :=
  sorry

/-- Compatibility of the constant 𝐅₂-family on overlapping characteristic level
sets. -/
theorem supportLevelFamily_compatible {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) ⦃W : X.Etale⦄ ⦃i j : ZMod 2⦄
    (a : W ⟶ supportLevelEtale Z hZ i) (b : W ⟶ supportLevelEtale Z hZ j)
    (hab : a ≫ supportLevelHom Z hZ i = b ≫ supportLevelHom Z hZ j) :
    supportLevelFamily Z hZ i ≫ (constantF2 X).obj.map a.op =
      supportLevelFamily Z hZ j ≫ (constantF2 X).obj.map b.op :=
  sorry

/-- The 𝐅₂-section of a clopen `Z ⊆ U` obtained by amalgamating the constant
values `1` on `Z` and `0` on the complement. -/
def characteristicSection {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) :
    (constantF2 X).obj.obj (op U) :=
  ((constantF2 X).property.amalgamateOfArrows (supportLevelHom Z hZ)
        (supportLevel_covers Z hZ) (supportLevelFamily Z hZ)
        (supportLevelFamily_compatible Z hZ)).hom
    (ULift.up (1 : ZMod 2))

/-- `characteristicSection` is the amalgamation of the characteristic level-set
family. -/
theorem characteristicSection_eq {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) :
    characteristicSection Z hZ =
      ((constantF2 X).property.amalgamateOfArrows (supportLevelHom Z hZ)
            (supportLevel_covers Z hZ) (supportLevelFamily Z hZ)
            (supportLevelFamily_compatible Z hZ)).hom
        (ULift.up (1 : ZMod 2)) :=
  sorry

/-- Restricting `characteristicSection` to `Z` yields the constant value `1`. -/
theorem characteristicSection_restrict_one {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) :
    (constantF2 X).obj.map (supportLevelHom Z hZ 1).op (characteristicSection Z hZ) =
      (constantF2ToSheafify (supportLevelEtale Z hZ 1)).hom (ULift.up (1 : ZMod 2)) :=
  sorry

/-- Restricting `characteristicSection` to the complement of `Z` yields the constant
value `0`. -/
theorem characteristicSection_restrict_zero {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) :
    (constantF2 X).obj.map (supportLevelHom Z hZ 0).op (characteristicSection Z hZ) =
      (constantF2ToSheafify (supportLevelEtale Z hZ 0)).hom (ULift.up (0 : ZMod 2)) :=
  sorry

/-- The étale support of `characteristicSection Z` is `Z`. -/
theorem characteristicSection_support {U : X.Etale} (Z : U.left.Opens)
    (hZ : IsClosed Z.carrier) :
    (abelianSheafSectionSupport (constantF2 X) U (characteristicSection Z hZ)).carrier =
      Z.carrier :=
  sorry

/-- Intersection of compactly supported 𝐅₂-supports remains closed. -/
theorem isClosed_sectionSupport_inter (V : Y.Etale)
    (σ τ : compactSupportSections f (constantF2 X) V) :
    IsClosed (sectionSupportSet f V σ ∩ sectionSupportSet f V τ) :=
  sorry

/-- Pointwise 𝐅₂-multiplication of compactly supported sections, as the characteristic
section of the intersection of supports. -/
def sectionMul (V : Y.Etale)
    (σ τ : compactSupportSections f (constantF2 X) V) :
    compactSupportSections f (constantF2 X) V :=
  ⟨characteristicSection (sectionSupportOpens f V σ ⊓ sectionSupportOpens f V τ)
      (isClosed_sectionSupport_inter f V σ τ),
    sorry⟩

/-- The underlying section of `sectionMul` is the characteristic section of the
intersection of supports. -/
theorem sectionMul_val (V : Y.Etale)
    (σ τ : compactSupportSections f (constantF2 X) V) :
    ((compactSupportSections f (constantF2 X) V).subtype (sectionMul f V σ τ)) =
      characteristicSection (sectionSupportOpens f V σ ⊓ sectionSupportOpens f V τ)
        (isClosed_sectionSupport_inter f V σ τ) :=
  sorry

/-- `sectionMul` is pointwise multiplication of 𝐅₂-sections: the product is nonzero
exactly on the intersection of the two supports. -/
theorem sectionMul_pointwise (V : Y.Etale)
    (σ τ : compactSupportSections f (constantF2 X) V)
    (ū : Scheme.GeometricPoint ((smallEtalePullback f).obj V).left) :
    geometricGerm ((smallEtalePullback f).obj V) (constantF2 X)
          ((compactSupportSections f (constantF2 X) V).subtype (sectionMul f V σ τ)) ū ≠
        0 ↔
      geometricGerm ((smallEtalePullback f).obj V) (constantF2 X)
            ((compactSupportSections f (constantF2 X) V).subtype σ) ū ≠ 0 ∧
        geometricGerm ((smallEtalePullback f).obj V) (constantF2 X)
            ((compactSupportSections f (constantF2 X) V).subtype τ) ū ≠ 0 :=
  sorry

/-- The support of `sectionMul σ τ` is the intersection of the two supports. -/
theorem sectionMul_support (V : Y.Etale)
    (σ τ : compactSupportSections f (constantF2 X) V) :
    sectionSupportSet f V (sectionMul f V σ τ) =
      sectionSupportSet f V σ ∩ sectionSupportSet f V τ :=
  sorry

/-- The scheme-side support of a finite-part pair is closed in the fibre. -/
theorem isClosed_schemeSupportOpens (V : Y.Etale)
    (p : Point (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V)) :
    IsClosed (schemeSupportOpens f V p).carrier :=
  sorry

/-- The compactly supported 𝐅₂-section associated to a finite-part pair, as the
characteristic function of `Z`. -/
def ofFinitePart (V : Y.Etale)
    (p : Point (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V)) :
    compactSupportSections f (constantF2 X) V :=
  ⟨characteristicSection (schemeSupportOpens f V p)
      (isClosed_schemeSupportOpens f V p),
    sorry⟩

/-- The underlying 𝐅₂-section of `ofFinitePart` is the characteristic section of
the scheme-side support. -/
theorem ofFinitePart_val (V : Y.Etale)
    (p : Point (ofSchemeHom f) ((Scheme.Etale.forget Y).obj V)) :
    ((compactSupportSections f (constantF2 X) V).subtype (ofFinitePart f V p)) =
      characteristicSection (schemeSupportOpens f V p)
        (isClosed_schemeSupportOpens f V p) :=
  sorry

/-- `ofFinitePart` is a sectionwise inverse of `ofSection`. -/
theorem ofFinitePart_ofSection (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    ofFinitePart f V (ofSection f V σ) = σ :=
  sorry

/-- Proper support of a compactly supported 𝐅₂-section, together with local
quasi-finiteness, upgrades `Z ⟶ V` to a finite morphism of algebraic spaces. -/
theorem isFinite_support_of_lowerShriekF2 [AlgebraicGeometry.IsSeparated f]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] (V : Y.Etale)
    (σ : compactSupportSections f (constantF2 X) V) :
    IsFinite (ofSection f V σ).pr0 :=
  sorry

variable [AlgebraicGeometry.IsSeparated f] [LocallyQuasiFinite f]
  [LocallyOfFiniteType f]

/-- The type equivalence between compactly supported 𝐅₂-sections of `f_!` and
finite-part pairs over an étale `Y`-scheme. -/
def lowerShriekF2Equiv (V : Y.Etale) :
    (CategoryTheory.forget AddCommGrpCat.{u}).obj
        (((etaleLowerShriek f).obj (constantF2 X)).obj.obj (op V)) ≃
      (finitePartEtale f).obj.obj (op V) where
  toFun σ := equivShrink _ (ofSection f V σ)
  invFun p := ofFinitePart f V ((equivShrink _).symm p)
  left_inv := sorry
  right_inv := sorry

/-- `lowerShriekF2Equiv` sends a compactly supported section to the shrunk
finite-part pair of `ofSection`. -/
theorem lowerShriekF2Equiv_apply (V : Y.Etale)
    (σ :
      (CategoryTheory.forget AddCommGrpCat.{u}).obj
        (((etaleLowerShriek f).obj (constantF2 X)).obj.obj (op V))) :
    lowerShriekF2Equiv f V σ = equivShrink _ (ofSection f V σ) :=
  sorry

/-- The inverse of `lowerShriekF2Equiv` is `ofFinitePart` after unshrinking. -/
theorem lowerShriekF2Equiv_symm_apply (V : Y.Etale)
    (p : (finitePartEtale f).obj.obj (op V)) :
    (lowerShriekF2Equiv f V).symm p =
      ofFinitePart f V ((equivShrink _).symm p) :=
  sorry

/-- The comparison isomorphism `f_! 𝐅₂ ≅ (X/Y)_fin` on the small étale site of
`Y`, after forgetting abelian coefficients. -/
def lowerShriekF2Iso :
    ((etaleLowerShriek f).obj (constantF2 X)).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u} ≅
      (finitePartEtale f).obj :=
  NatIso.ofComponents (fun V ↦ Equiv.toIso (lowerShriekF2Equiv f V.unop)) sorry

/-- `lowerShriekF2Iso` sends a compactly supported 𝐅₂-section to the shrunk
finite-part pair of `ofSection`. -/
theorem lowerShriekF2Iso_hom_app (V : Y.Etale)
    (σ :
      (CategoryTheory.forget AddCommGrpCat.{u}).obj
        (((etaleLowerShriek f).obj (constantF2 X)).obj.obj (op V))) :
    (lowerShriekF2Iso f).hom.app (op V) σ = equivShrink _ (ofSection f V σ) :=
  sorry

/-- Inverse components of `lowerShriekF2Iso` recover `ofFinitePart`. -/
theorem lowerShriekF2Iso_inv_app (V : Y.Etale)
    (p : (finitePartEtale f).obj.obj (op V)) :
    (lowerShriekF2Iso f).inv.app (op V) p =
      ofFinitePart f V ((equivShrink _).symm p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
