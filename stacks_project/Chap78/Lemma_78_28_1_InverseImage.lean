module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_15_1_InverseImage
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Inverse image of groupoids in algebraic spaces

Algebraic spaces and groupoids on a contained site `(C, J)` over `S` are packaged as sheaves
on `J.over S` with the atlas/diagonal data of `AlgebraicSpace.ofInverseImage`. Inverse image
along `slicePost ι S` is sheaf pullback, sent to algebraic spaces over `ι.obj S` by
`ofInverseImage`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open Functor.relativelyRepresentable MorphismProperty Opposite

noncomputable section

universe u uC

namespace AlgebraicGeometry.AlgebraicSpace

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (S : C)
variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι S).IsContinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj S)) (Type u)]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type u, (slicePost ι S).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι S).sheafPullback (Type u) (J.over S)
    (Scheme.fppfTopology.over (ι.obj S)))]
variable [HasPullbacks (Sheaf (J.over S) (Type u))]

/-- An algebraic space on a contained big site, given as a sheaf on `J.over S` with representable
diagonal and a representable étale locally surjective atlas in the sense of
`AlgebraicSpace.ofInverseImage`. -/
structure OnSlice where
  /-- The underlying sheaf on the smaller slice. -/
  sheaf : Sheaf (J.over S) (Type u)
  /-- The diagonal of the sheaf is representable by schemes. -/
  representableDiagonal : yoneda.relativelyRepresentable (Limits.diag sheaf.obj)
  /-- A scheme over `S` presenting an étale atlas. -/
  atlasScheme : Over S
  /-- The atlas morphism from the representing scheme. -/
  atlas : yoneda.obj atlasScheme ⟶ sheaf.obj
  /-- The atlas is representable by schemes. -/
  atlas_representable : yoneda.relativelyRepresentable atlas
  /-- After inclusion into the large slice, the atlas is étale. -/
  atlas_etale : ∀ {V : Over S} (ξ : yoneda.obj V ⟶ sheaf.obj),
    (MorphismProperty.over (@Etale)) ((slicePost ι S).map (atlas_representable.snd ξ))
  /-- After inclusion into the large slice, the atlas is étale-locally surjective. -/
  atlas_surjective : ∀ {V : Over S} (ξ : yoneda.obj V ⟶ sheaf.obj),
    Surjective ((slicePost ι S).map (atlas_representable.snd ξ)).left

/-- The algebraic space over `ι.obj S` obtained by inverse image of an algebraic-space sheaf on
the contained site. -/
def OnSlice.toAlgebraicSpace (F : OnSlice ι J S) : AlgebraicSpace (ι.obj S) :=
  ofInverseImage ι J S F.sheaf F.representableDiagonal F.atlas F.atlas_representable
    F.atlas_etale F.atlas_surjective

/-- A representable sheaf `yoneda.obj T` on the contained slice, viewed as an algebraic space
on that site with identity atlas. -/
def OnSlice.ofYoneda (T : Over S) : OnSlice ι J S where
  sheaf := (J.over S).yoneda.obj T
  representableDiagonal := sorry
  atlasScheme := T
  atlas := 𝟙 (yoneda.obj T)
  atlas_representable := sorry
  atlas_etale := sorry
  atlas_surjective := sorry

/-- The functor of points of `OnSlice.toAlgebraicSpace F` is the underlying presheaf of the
sheaf inverse image of `F`. -/
theorem OnSlice.toAlgebraicSpace_functorOfPoints (F : OnSlice ι J S) :
    (F.toAlgebraicSpace).functorOfPoints =
      ((inverseImage ι S J Scheme.fppfTopology).obj F.sheaf).obj := sorry

/-- A section of a contained-site algebraic space over `T`, viewed as a point of its inverse
image over the included scheme `slicePost.obj T`. -/
def OnSlice.sectionPoint (F : OnSlice ι J S) (T : Over S) (x : F.sheaf.obj.obj (op T)) :
    AlgebraicSpace.Hom (ofOver ((slicePost ι S).obj T)) F.toAlgebraicSpace :=
  inverseImageAtlasHom ι S J Scheme.fppfTopology ((J.over S).yonedaEquiv.symm x).hom

/-- The underlying presheaf morphism of `OnSlice.sectionPoint` is `inverseImageAtlasHom` of the
Yoneda morphism of the given section. -/
theorem OnSlice.sectionPoint_hom (F : OnSlice ι J S) (T : Over S)
    (x : F.sheaf.obj.obj (op T)) :
    OnSlice.sectionPoint ι J S F T x =
      inverseImageAtlasHom ι S J Scheme.fppfTopology
        ((J.over S).yonedaEquiv.symm x).hom := sorry

/-- Inverse image of a morphism of algebraic-space sheaves on the contained site. -/
def inverseImageHom {F G : OnSlice ι J S} (f : F.sheaf ⟶ G.sheaf) :
    F.toAlgebraicSpace ⟶ G.toAlgebraicSpace :=
  ((inverseImage ι S J Scheme.fppfTopology).map f).hom

/-- Inverse image of an object of `Over` in algebraic-space sheaves. -/
def inverseImageOver (B U : OnSlice ι J S) (f : U.sheaf ⟶ B.sheaf) :
    Over (B.toAlgebraicSpace) :=
  Over.mk (inverseImageHom ι J S f)

/-- Inverse image of a morphism over a base algebraic-space sheaf. -/
def inverseImageOverHom (B U V : OnSlice ι J S)
    (uHom : U.sheaf ⟶ B.sheaf) (vHom : V.sheaf ⟶ B.sheaf)
    (f : U.sheaf ⟶ V.sheaf) :
    inverseImageOver ι J S B U uHom ⟶ inverseImageOver ι J S B V vHom :=
  Over.homMk (inverseImageHom ι J S f) sorry

/-- Sheaf inverse image preserves fibre products of morphisms of algebraic-space sheaves. -/
def inverseImage_pullbackIso {U R : OnSlice ι J S} (s t : R.sheaf ⟶ U.sheaf) :
    (inverseImage ι S J Scheme.fppfTopology).obj (pullback s t) ≅
      pullback ((inverseImage ι S J Scheme.fppfTopology).map s)
        ((inverseImage ι S J Scheme.fppfTopology).map t) :=
  PreservesPullback.iso (inverseImage ι S J Scheme.fppfTopology) s t

/-- Inverse image of a composition morphism as a sheaf morphism, transported along the
preserved fibre product. -/
def inverseImageCompHom {U R : OnSlice ι J S} {s t : R.sheaf ⟶ U.sheaf}
    (c : pullback s t ⟶ R.sheaf) :
    pullback ((inverseImage ι S J Scheme.fppfTopology).map s)
        ((inverseImage ι S J Scheme.fppfTopology).map t) ⟶
      (inverseImage ι S J Scheme.fppfTopology).obj R.sheaf :=
  (inverseImage_pullbackIso ι J S s t).inv ≫
    (inverseImage ι S J Scheme.fppfTopology).map c

/-- The underlying presheaf of the sheaf fibre product of inverse images is the fibre product
of the underlying inverse-image morphisms. -/
def inverseImagePullback_presheafIso {U R : OnSlice ι J S} (s t : R.sheaf ⟶ U.sheaf) :
    (pullback ((inverseImage ι S J Scheme.fppfTopology).map s)
        ((inverseImage ι S J Scheme.fppfTopology).map t)).obj ≅
      pullback (inverseImageHom ι J S s) (inverseImageHom ι J S t) :=
  PreservesPullback.iso
    (sheafToPresheaf (Scheme.fppfTopology.over (ι.obj S)) (Type u))
    ((inverseImage ι S J Scheme.fppfTopology).map s)
    ((inverseImage ι S J Scheme.fppfTopology).map t)

/-- Inverse image of composition as a morphism of algebraic spaces: lift the AlgebraicSpace
fibre product to the sheaf fibre product, then apply `inverseImageCompHom`. -/
def inverseImageCompHom_algebraic {U R : OnSlice ι J S} {s t : R.sheaf ⟶ U.sheaf}
    (c : pullback s t ⟶ R.sheaf) :
    pullback (inverseImageHom ι J S s) (inverseImageHom ι J S t) ⟶ R.toAlgebraicSpace :=
  (pullback.lift
        (pullback.fst (inverseImageHom ι J S s) (inverseImageHom ι J S t) :
          (pullback (inverseImageHom ι J S s) (inverseImageHom ι J S t)).functorOfPoints ⟶
            R.toAlgebraicSpace.functorOfPoints)
        (pullback.snd (inverseImageHom ι J S s) (inverseImageHom ι J S t) :
          (pullback (inverseImageHom ι J S s) (inverseImageHom ι J S t)).functorOfPoints ⟶
            R.toAlgebraicSpace.functorOfPoints)
        sorry ≫
      (inverseImagePullback_presheafIso ι J S s t).inv ≫
        Sheaf.homEquiv (inverseImageCompHom ι J S c) :
    (pullback (inverseImageHom ι J S s) (inverseImageHom ι J S t)).functorOfPoints ⟶
      R.toAlgebraicSpace.functorOfPoints)

/-- Inverse image of composition as a morphism over the inverse-image base. -/
def inverseImageOverComp (B U R : OnSlice ι J S)
    (uHom : U.sheaf ⟶ B.sheaf) (rHom : R.sheaf ⟶ B.sheaf)
    (s t : R.sheaf ⟶ U.sheaf) (c : pullback s t ⟶ R.sheaf) :
    pullback (inverseImageOverHom ι J S B R U rHom uHom s)
      (inverseImageOverHom ι J S B R U rHom uHom t) ⟶
      inverseImageOver ι J S B R rHom :=
  Over.homMk
    ((PreservesPullback.iso (Over.forget B.toAlgebraicSpace)
        (inverseImageOverHom ι J S B R U rHom uHom s)
        (inverseImageOverHom ι J S B R U rHom uHom t)).hom ≫
      inverseImageCompHom_algebraic ι J S c)
    sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

open AlgebraicGeometry.AlgebraicSpace

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (S : C)
variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι S).IsContinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj S)) (Type u)]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type u, (slicePost ι S).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι S).sheafPullback (Type u) (J.over S)
    (Scheme.fppfTopology.over (ι.obj S)))]
variable [HasPullbacks (Sheaf (J.over S) (Type u))]

/-- A groupoid in algebraic spaces on a contained big site over `S`: object and arrow sheaves
that are algebraic spaces in the sense of `OnSlice`, together with source, target, composition,
identity, and inverse. -/
structure GroupoidOnSlice where
  /-- The base algebraic space on the contained site. -/
  B : AlgebraicSpace.OnSlice ι J S
  /-- The algebraic space of objects. -/
  U : AlgebraicSpace.OnSlice ι J S
  /-- The algebraic space of arrows. -/
  R : AlgebraicSpace.OnSlice ι J S
  /-- The structure map of the object space over the base. -/
  U_hom : U.sheaf ⟶ B.sheaf
  /-- The structure map of the arrow space over the base. -/
  R_hom : R.sheaf ⟶ B.sheaf
  /-- The source map. -/
  s : R.sheaf ⟶ U.sheaf
  /-- The target map. -/
  t : R.sheaf ⟶ U.sheaf
  /-- Composition of composable arrows. -/
  c : pullback s t ⟶ R.sheaf
  /-- The identity-arrow map. -/
  e : U.sheaf ⟶ R.sheaf
  /-- The inverse-arrow map. -/
  i : R.sheaf ⟶ R.sheaf
  /-- Source is a morphism over the base. -/
  s_over : s ≫ U_hom = R_hom
  /-- Target is a morphism over the base. -/
  t_over : t ≫ U_hom = R_hom
  /-- The source of a composite is the source of its earlier arrow. -/
  comp_source : c ≫ s = pullback.snd s t ≫ s
  /-- The target of a composite is the target of its later arrow. -/
  comp_target : c ≫ t = pullback.fst s t ≫ t
  /-- Identity arrows have the specified source. -/
  identity_source : e ≫ s = 𝟙 U.sheaf
  /-- Identity arrows have the specified target. -/
  identity_target : e ≫ t = 𝟙 U.sheaf
  /-- Inversion exchanges source with target. -/
  inverse_source : i ≫ s = t
  /-- Inversion exchanges target with source. -/
  inverse_target : i ≫ t = s
  /-- Composition is associative on every test sheaf. -/
  associativity :
    ∀ {T : Sheaf (J.over S) (Type u)} (a b d : T ⟶ R.sheaf)
      (h_ab : a ≫ s = b ≫ t) (h_bd : b ≫ s = d ≫ t)
      (h_ab_d : (pullback.lift a b h_ab ≫ c) ≫ s = d ≫ t)
      (h_a_bd : a ≫ s = (pullback.lift b d h_bd ≫ c) ≫ t),
      pullback.lift (pullback.lift a b h_ab ≫ c) d h_ab_d ≫ c =
        pullback.lift a (pullback.lift b d h_bd ≫ c) h_a_bd ≫ c
  /-- Composing an arrow with the identity at its source does not change it. -/
  right_identity :
    ∀ {T : Sheaf (J.over S) (Type u)} (a : T ⟶ R.sheaf)
      (h : a ≫ s = ((a ≫ s) ≫ e) ≫ t),
      pullback.lift a ((a ≫ s) ≫ e) h ≫ c = a
  /-- Composing the identity at the target of an arrow with that arrow does not change it. -/
  left_identity :
    ∀ {T : Sheaf (J.over S) (Type u)} (a : T ⟶ R.sheaf)
      (h : ((a ≫ t) ≫ e) ≫ s = a ≫ t),
      pullback.lift ((a ≫ t) ≫ e) a h ≫ c = a
  /-- Composing an arrow after its inverse gives the identity at its target. -/
  inverse_comp :
    ∀ {T : Sheaf (J.over S) (Type u)} (a : T ⟶ R.sheaf)
      (h : a ≫ s = (a ≫ i) ≫ t),
      pullback.lift a (a ≫ i) h ≫ c = (a ≫ t) ≫ e
  /-- Composing the inverse of an arrow after it gives the identity at its source. -/
  comp_inverse :
    ∀ {T : Sheaf (J.over S) (Type u)} (a : T ⟶ R.sheaf)
      (h : (a ≫ i) ≫ s = a ≫ t),
      pullback.lift (a ≫ i) a h ≫ c = (a ≫ s) ≫ e

/-- The discrete groupoid in algebraic spaces on a contained-site algebraic space. -/
def GroupoidOnSlice.discrete (X : AlgebraicSpace.OnSlice ι J S) : GroupoidOnSlice ι J S where
  B := X
  U := X
  R := X
  U_hom := 𝟙 X.sheaf
  R_hom := 𝟙 X.sheaf
  s := 𝟙 X.sheaf
  t := 𝟙 X.sheaf
  c := pullback.fst (𝟙 X.sheaf) (𝟙 X.sheaf)
  e := 𝟙 X.sheaf
  i := 𝟙 X.sheaf
  s_over := sorry
  t_over := sorry
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- Inverse image of a groupoid in algebraic spaces along an enlargement of big sites, obtained
by applying `ofInverseImage` to the object space, arrow space, and structure maps. The
composition field is the Over-morphism whose left component is the sheaf inverse image of
composition, after identifying fibre products via `inverseImage_pullbackIso`. -/
def GroupoidOnSlice.inverseImage (G : GroupoidOnSlice ι J S) : GroupoidAlgebraicSpace G.B.toAlgebraicSpace where
  U := inverseImageOver ι J S G.B G.U G.U_hom
  R := inverseImageOver ι J S G.B G.R G.R_hom
  s := inverseImageOverHom ι J S G.B G.R G.U G.R_hom G.U_hom G.s
  t := inverseImageOverHom ι J S G.B G.R G.U G.R_hom G.U_hom G.t
  c := inverseImageOverComp ι J S G.B G.U G.R G.U_hom G.R_hom G.s G.t G.c
  e := inverseImageOverHom ι J S G.B G.U G.R G.U_hom G.R_hom G.e
  i := inverseImageOverHom ι J S G.B G.R G.R G.R_hom G.R_hom G.i
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object space of the inverse-image groupoid is `ofInverseImage` of the small object
space. -/
theorem inverseImage_U (G : GroupoidOnSlice ι J S) :
    (G.inverseImage).U.left = G.U.toAlgebraicSpace := sorry

/-- The arrow space of the inverse-image groupoid is `ofInverseImage` of the small arrow
space. -/
theorem inverseImage_R (G : GroupoidOnSlice ι J S) :
    (G.inverseImage).R.left = G.R.toAlgebraicSpace := sorry

/-- Inverse image preserves the source map of a groupoid in algebraic spaces. -/
theorem inverseImage_s (G : GroupoidOnSlice ι J S) :
    (G.inverseImage).s.left = inverseImageHom ι J S G.s := sorry

/-- Inverse image preserves the target map of a groupoid in algebraic spaces. -/
theorem inverseImage_t (G : GroupoidOnSlice ι J S) :
    (G.inverseImage).t.left = inverseImageHom ι J S G.t := sorry

/-- Inverse image of composition, as a sheaf morphism, is the original composition transported
along the preserved fibre product. -/
theorem inverseImage_c (G : GroupoidOnSlice ι J S) :
    inverseImageCompHom ι J S G.c =
      (inverseImage_pullbackIso ι J S G.s G.t).inv ≫
        (inverseImage ι S J Scheme.fppfTopology).map G.c := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
