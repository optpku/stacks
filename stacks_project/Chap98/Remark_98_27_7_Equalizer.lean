module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap87.Lemma_87_14_5_Reduction
public import stacks_project.Chap88.Definition_88_24_1_Modification
public import stacks_project.Chap88.Lemma_88_25_5_MapAlong
public import stacks_project.Chap98.Lemma_98_27_4_Functor
public import stacks_project.Chap98.Lemma_98_27_4_Triple
public import stacks_project.Chap98.Lemma_98_27_6_Solution

/-!
# Diagonal equalizers of contraction triples

Given two compatible triples on a locally Noetherian scheme `V` over `S`, the
fibre product of interpolating dilatations, the equalizer of the interpolating
maps into `X'`, and the equalizer of the completed maps into `W` assemble into
the diagonal equalizer data used to represent the fibre product of the
contraction functor along its diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.openComplementAlong

/-- If `T ≤ T'`, the open complement of `T'` includes into the open complement of
`T`. -/
def mapOfLe {S : Scheme.{u}} {X : AlgebraicSpace S} {T T' : Closeds (Points X)}
    (h : T ≤ T') :
    openComplementAlong X T' ⟶ openComplementAlong X T where
  app U := ofHom fun x ↦ ⟨x.1, sorry⟩
  naturality := sorry

/-- Postcomposing `mapOfLe h` with the open-complement inclusion of `T` recovers
the open-complement inclusion of `T'`. -/
theorem mapOfLe_comp_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T T' : Closeds (Points X)} (h : T ≤ T') :
    mapOfLe h ≫ AlgebraicSpace.openComplementι X T =
      AlgebraicSpace.openComplementι X T' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.openComplementAlong

namespace AlgebraicGeometry.AlgebraicSpace

/-- A field-valued point of `baseChange g X` determines a field-valued point of
`X` by postcomposing the structure morphism with `g`. -/
def fieldValuedPoint_baseChange {S S' : Scheme.{u}} (g : S ⟶ S')
    {X : AlgebraicSpace S'} (p : FieldValuedPoint (baseChange g X)) :
    FieldValuedPoint X where
  K := p.K
  structureHom := p.structureHom ≫ g
  hom :=
    yonedaEquiv.symm
      (p.hom.app (op p.overObj) (yonedaEquiv (𝟙 (ofOver p.overObj))) :
        X.functorOfPoints.obj (op ((Over.map g).obj p.overObj)))

/-- The map on points induced by viewing an algebraic space over `S'` as an
algebraic space over `S` along `g`. -/
def pointsBaseChange {S S' : Scheme.{u}} (g : S ⟶ S') (X : AlgebraicSpace S') :
    Points (baseChange g X) → Points X :=
  Quotient.map (fieldValuedPoint_baseChange g) fun _ _ _ ↦ sorry

/-- `pointsBaseChange g X` is continuous. -/
theorem continuous_pointsBaseChange {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : AlgebraicSpace S') : Continuous (pointsBaseChange g X) :=
  sorry

/-- The structure morphism of a scheme over `V` commutes with the forgetful map
to schemes over `S`. -/
theorem overHom_w {S : Scheme.{u}} (V : Over S) (A : Over V.left) :
    A.hom ≫ V.hom = ((Over.map V.hom).obj A).hom :=
  sorry

/-- The morphism over `S` from a scheme over `V` to `V`. -/
def overHom {S : Scheme.{u}} (V : Over S) (A : Over V.left) :
    (Over.map V.hom).obj A ⟶ V :=
  Over.homMk A.hom (overHom_w V A)

/-- Viewing a locally Noetherian scheme over `V` as a scheme over `S` preserves
local Noetherianity. -/
instance instIsLocallyNoetherian_overMap {S : Scheme.{u}} {V : Over S}
    (A : Over V.left) [AlgebraicGeometry.IsLocallyNoetherian A.left] :
    AlgebraicGeometry.IsLocallyNoetherian ((Over.map V.hom).obj A).left :=
  ‹AlgebraicGeometry.IsLocallyNoetherian A.left›

/-- A `T`-point of `X` over `V` is a map into `X` lying over the structure
morphism of `T`. -/
abbrev sliceSection {S : Scheme.{u}} {V : Over S} (X : AlgebraicSpace S)
    (f : X ⟶ ofOver V) (T : (Over V.left)ᵒᵖ) : Type u :=
  { x : X.functorOfPoints.obj (op ((Over.map V.hom).obj T.unop)) //
    f.app (op ((Over.map V.hom).obj T.unop)) x =
      yonedaEquiv (ofOverMap (overHom V T.unop)) }

/-- Restriction of slice sections along a morphism of schemes over `V`. -/
theorem sliceSection_map {S : Scheme.{u}} {V : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver V) {T T' : (Over V.left)ᵒᵖ} (φ : T ⟶ T')
    (x : sliceSection X f T) :
    f.app (op ((Over.map V.hom).obj T'.unop))
        (X.functorOfPoints.map ((Over.map V.hom).op.map φ) x.1) =
      yonedaEquiv (ofOverMap (overHom V T'.unop)) :=
  sorry

/-- The functor of `T`-points of `X` over `V` along `f : X ⟶ ofOver V`. -/
def slicePresheaf {S : Scheme.{u}} {V : Over S} (X : AlgebraicSpace S)
    (f : X ⟶ ofOver V) : (Over V.left)ᵒᵖ ⥤ Type u where
  obj T := sliceSection X f T
  map φ := ofHom fun x ↦
    ⟨X.functorOfPoints.map ((Over.map V.hom).op.map φ) x.1, sliceSection_map f φ x⟩
  map_id := sorry
  map_comp := sorry

/-- The algebraic space over `V` whose `T`-points are maps into `X` over `V`. -/
def sliceSpace {S : Scheme.{u}} {V : Over S} (X : AlgebraicSpace S)
    (f : X ⟶ ofOver V) : AlgebraicSpace V.left :=
  ofFunctor (slicePresheaf X f) sorry sorry sorry

/-- The functor of points of `sliceSpace X f` is `slicePresheaf X f`. -/
theorem sliceSpace_functorOfPoints {S : Scheme.{u}} {V : Over S}
    (X : AlgebraicSpace S) (f : X ⟶ ofOver V) :
    (sliceSpace X f).functorOfPoints = slicePresheaf X f :=
  sorry

/-- A field-valued point of `sliceSpace X f` determines a field-valued point of
`X` by composing the structure morphism with `V ⟶ S`. -/
def fieldValuedPoint_sliceSpace {S : Scheme.{u}} {V : Over S}
    {X : AlgebraicSpace S} (f : X ⟶ ofOver V)
    (p : FieldValuedPoint (sliceSpace X f)) : FieldValuedPoint X where
  K := p.K
  field := p.field
  structureHom := p.structureHom ≫ V.hom
  hom := yonedaEquiv.symm (p.elem).1

/-- Equivalence of field-valued points is preserved by `fieldValuedPoint_sliceSpace`. -/
theorem equivalent_fieldValuedPoint_sliceSpace {S : Scheme.{u}} {V : Over S}
    {X : AlgebraicSpace S} (f : X ⟶ ofOver V)
    {p q : FieldValuedPoint (sliceSpace X f)}
    (h : FieldValuedPoint.Equivalent p q) :
    FieldValuedPoint.Equivalent (fieldValuedPoint_sliceSpace f p)
      (fieldValuedPoint_sliceSpace f q) :=
  sorry

/-- The map on points from the slice of `X` over `V` to `X`. -/
def pointsSlice {S : Scheme.{u}} {V : Over S} (X : AlgebraicSpace S)
    (f : X ⟶ ofOver V) : Points (sliceSpace X f) → Points X :=
  Quotient.map (fieldValuedPoint_sliceSpace f)
    fun _ _ h ↦ equivalent_fieldValuedPoint_sliceSpace f h

/-- `pointsSlice X f` is continuous. -/
theorem continuous_pointsSlice {S : Scheme.{u}} {V : Over S}
    (X : AlgebraicSpace S) (f : X ⟶ ofOver V) :
    Continuous (pointsSlice X f) :=
  sorry

/-- A `T`-point of a presheaf over `V` is a section lying over the structure
morphism of `T`. -/
abbrev formalSliceSection {S : Scheme.{u}} {V : Over S}
    (F : (Over S)ᵒᵖ ⥤ Type u) (π : F ⟶ (ofOver V).functorOfPoints)
    (T : (Over V.left)ᵒᵖ) : Type u :=
  { y : F.obj (op ((Over.map V.hom).obj T.unop)) //
    π.app (op ((Over.map V.hom).obj T.unop)) y =
      yonedaEquiv (ofOverMap (overHom V T.unop)) }

/-- Restriction of formal slice sections along a morphism of schemes over `V`. -/
theorem formalSliceSection_map {S : Scheme.{u}} {V : Over S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (π : F ⟶ (ofOver V).functorOfPoints)
    {T T' : (Over V.left)ᵒᵖ} (φ : T ⟶ T') (y : formalSliceSection F π T) :
    π.app (op ((Over.map V.hom).obj T'.unop))
        (F.map ((Over.map V.hom).op.map φ) y.1) =
      yonedaEquiv (ofOverMap (overHom V T'.unop)) :=
  sorry

/-- The fibre over `V` of a presheaf on schemes over `S` equipped with a
morphism to `V`. -/
def formalSlicePresheaf {S : Scheme.{u}} {V : Over S}
    (F : (Over S)ᵒᵖ ⥤ Type u) (π : F ⟶ (ofOver V).functorOfPoints) :
    (Over V.left)ᵒᵖ ⥤ Type u where
  obj T := formalSliceSection F π T
  map φ := ofHom fun y ↦
    ⟨F.map ((Over.map V.hom).op.map φ) y.1, formalSliceSection_map π φ y⟩
  map_id := sorry
  map_comp := sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- The equalizer of interpolating maps `x'_i : V'_i ⟶ X'` and of completed maps
`hatx_i : V_{/Z_i} ⟶ W`, together with the comparison morphism from the
completion of `E'` along the inverse image of `Z = Z_1 ∩ Z_2`. -/
structure DiagonalEqualizer {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) where
  /-- The fibre product `V' = V'_1 ×_V V'_2`. -/
  pullbackSpace : AlgebraicSpace S
  /-- The equalizer `E'` of `V' ⟶ V'_i ⟶ X'`. -/
  space : AlgebraicSpace S
  /-- The structure morphism `E' ⟶ V`. -/
  toV : space ⟶ ofOver V
  /-- The equalized interpolating morphism `E' ⟶ X'`. -/
  spaceHom : space ⟶ σ.X'
  /-- The closed subset `Z = Z_1 ∩ Z_2`. -/
  closed : Closeds (Points (ofOver V))
  /-- The equalizer `E_W` of `V_{/Z} ⟶ V_{/Z_i} ⟶ W`. -/
  formal : (Over S)ᵒᵖ ⥤ Type u
  /-- The inclusion `E_W ⟶ V_{/Z}`. -/
  toFormal : formal ⟶ completionAlong (ofOver V) closed
  /-- The comparison `E'_{/Z} ⟶ E_W` through which `E'_{/Z} ⟶ V_{/Z}` factors. -/
  factor :
    completionAlong space (closed.preimage (Points.continuous_map toV)) ⟶ formal

namespace DiagonalEqualizer

variable {σ : ContractionSituation S} {V : Over S}
  [AlgebraicGeometry.IsLocallyNoetherian V.left]

/-- The fibre product `V'_1 ×_V V'_2` of interpolating dilatations. -/
def interpPullback (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) : AlgebraicSpace S :=
  pullback w1.toV w2.toV

/-- The interpolating map `V' ⟶ V'_1 ⟶ X'`. -/
def leftHom (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    interpPullback ξ1 ξ2 w1 w2 ⟶ σ.X' :=
  pullback.fst w1.toV w2.toV ≫ w1.x'

/-- The interpolating map `V' ⟶ V'_2 ⟶ X'`. -/
def rightHom (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    interpPullback ξ1 ξ2 w1 w2 ⟶ σ.X' :=
  pullback.snd w1.toV w2.toV ≫ w2.x'

/-- The pair morphism `(x'_1, x'_2) : V' ⟶ X' ⨯ X'`. -/
def pairHom (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    interpPullback ξ1 ξ2 w1 w2 ⟶ σ.X' ⨯ σ.X' :=
  prod.lift (leftHom ξ1 ξ2 w1 w2) (rightHom ξ1 ξ2 w1 w2)

/-- The diagonal morphism `X' ⟶ X' ⨯ X'`. -/
def diagHom (σ : ContractionSituation S) : σ.X' ⟶ σ.X' ⨯ σ.X' :=
  prod.lift (𝟙 σ.X') (𝟙 σ.X')

/-- The equalizer `E'` of the interpolating maps into `X'`. -/
def interpSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) : AlgebraicSpace S :=
  pullback (pairHom ξ1 ξ2 w1 w2) (diagHom σ)

/-- The structure morphism `E' ⟶ V`. -/
def interpToV (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    interpSpace ξ1 ξ2 w1 w2 ⟶ ofOver V :=
  pullback.fst (pairHom ξ1 ξ2 w1 w2) (diagHom σ) ≫
    pullback.fst w1.toV w2.toV ≫ w1.toV

/-- The closed subset `Z = Z_1 ∩ Z_2`. -/
def interClosed (ξ1 ξ2 : Triple σ V) : Closeds (Points (ofOver V)) :=
  ξ1.Z ⊓ ξ2.Z

/-- The identity on `V` sends `Z` into `Z_1`. -/
theorem interClosed_subset_left (ξ1 ξ2 : Triple σ V) :
    Points.map (𝟙 (ofOver V)) ''
        ((interClosed ξ1 ξ2 : Closeds (Points (ofOver V))) : Set _) ⊆
      (ξ1.Z : Set (Points (ofOver V))) :=
  sorry

/-- The identity on `V` sends `Z` into `Z_2`. -/
theorem interClosed_subset_right (ξ1 ξ2 : Triple σ V) :
    Points.map (𝟙 (ofOver V)) ''
        ((interClosed ξ1 ξ2 : Closeds (Points (ofOver V))) : Set _) ⊆
      (ξ2.Z : Set (Points (ofOver V))) :=
  sorry

/-- The completed map `V_{/Z} ⟶ V_{/Z_1} ⟶ W`. -/
def leftHat (ξ1 ξ2 : Triple σ V) :
    completionAlong (ofOver V) (interClosed ξ1 ξ2) ⟶ σ.W :=
  completionAlong.mapOfLe (𝟙 (ofOver V)) (interClosed ξ1 ξ2) ξ1.Z
      (interClosed_subset_left ξ1 ξ2) ≫
    ξ1.hatx

/-- The completed map `V_{/Z} ⟶ V_{/Z_2} ⟶ W`. -/
def rightHat (ξ1 ξ2 : Triple σ V) :
    completionAlong (ofOver V) (interClosed ξ1 ξ2) ⟶ σ.W :=
  completionAlong.mapOfLe (𝟙 (ofOver V)) (interClosed ξ1 ξ2) ξ2.Z
      (interClosed_subset_right ξ1 ξ2) ≫
    ξ2.hatx

/-- The equalizer `E_W` of the completed maps into `W`. -/
def interpFormal (ξ1 ξ2 : Triple σ V) : (Over S)ᵒᵖ ⥤ Type u :=
  equalizer (leftHat ξ1 ξ2) (rightHat ξ1 ξ2)

/-- The inclusion `E_W ⟶ V_{/Z}`. -/
def interpToFormal (ξ1 ξ2 : Triple σ V) :
    interpFormal ξ1 ξ2 ⟶ completionAlong (ofOver V) (interClosed ξ1 ξ2) :=
  equalizer.ι (leftHat ξ1 ξ2) (rightHat ξ1 ξ2)

/-- The underlying points of `V` in the image of `equalizer.ι : E_W ⟶ V_{/Z}`. -/
def hatEqualizerImage (ξ1 ξ2 : Triple σ V) : Set (Points (ofOver V)) :=
  { p | ∃ (q : FieldValuedPoint (ofOver V))
      (hp : mapsInto (interClosed ξ1 ξ2 : Set (Points (ofOver V))) q.elem)
      (y : (interpFormal ξ1 ξ2).obj (op q.overObj)),
      (interpToFormal ξ1 ξ2).app (op q.overObj) y = ⟨q.elem, hp⟩ ∧
        Points.mk q = p }

/-- Membership in `hatEqualizerImage` means a field-valued representative of the
point of `V` lifts through `equalizer.ι`. -/
theorem mem_hatEqualizerImage (ξ1 ξ2 : Triple σ V)
    (p : Points (ofOver V)) :
    p ∈ hatEqualizerImage ξ1 ξ2 ↔
      ∃ (q : FieldValuedPoint (ofOver V))
        (hp : mapsInto (interClosed ξ1 ξ2 : Set (Points (ofOver V))) q.elem)
        (y : (interpFormal ξ1 ξ2).obj (op q.overObj)),
        (interpToFormal ξ1 ξ2).app (op q.overObj) y = ⟨q.elem, hp⟩ ∧
          Points.mk q = p :=
  sorry

/-- The closed subset of `Z = Z_1 ∩ Z_2` consisting of points of `V_{/Z}` that
equalize `leftHat` and `rightHat`. -/
def hatEqualizerClosed (ξ1 ξ2 : Triple σ V) : Closeds (Points (ofOver V)) where
  carrier := hatEqualizerImage ξ1 ξ2
  isClosed' := sorry

/-- The carrier of `hatEqualizerClosed` is the image of `equalizer.ι`. -/
theorem hatEqualizerClosed_carrier (ξ1 ξ2 : Triple σ V) :
    (hatEqualizerClosed ξ1 ξ2 : Set (Points (ofOver V))) =
      hatEqualizerImage ξ1 ξ2 :=
  sorry

/-- The identity on `V` sends the equalizer image into `Z = Z_1 ∩ Z_2`. -/
theorem hatEqualizerClosed_subset (ξ1 ξ2 : Triple σ V) :
    Points.map (𝟙 (ofOver V)) ''
        ((hatEqualizerClosed ξ1 ξ2 : Closeds (Points (ofOver V))) : Set _) ⊆
      (interClosed ξ1 ξ2 : Set (Points (ofOver V))) :=
  sorry

/-- The inverse image of `Z` along `E' ⟶ V`. -/
def spaceClosed (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Closeds (Points (interpSpace ξ1 ξ2 w1 w2)) :=
  (interClosed ξ1 ξ2).preimage (Points.continuous_map (interpToV ξ1 ξ2 w1 w2))

/-- Completing `E' ⟶ V` along `Z` equalizes the two completed maps into `W`. -/
theorem map_comp_equalizes (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    completionAlong.map (interpToV ξ1 ξ2 w1 w2) (interClosed ξ1 ξ2) ≫
        leftHat ξ1 ξ2 =
      completionAlong.map (interpToV ξ1 ξ2 w1 w2) (interClosed ξ1 ξ2) ≫
        rightHat ξ1 ξ2 :=
  sorry

/-- The comparison `E'_{/Z} ⟶ E_W`. -/
def interpFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    completionAlong (interpSpace ξ1 ξ2 w1 w2) (spaceClosed ξ1 ξ2 w1 w2) ⟶
      interpFormal ξ1 ξ2 :=
  equalizer.lift (completionAlong.map (interpToV ξ1 ξ2 w1 w2) (interClosed ξ1 ξ2))
    (map_comp_equalizes ξ1 ξ2 w1 w2)

/-- Package the constructed fibre product, equalizers, and comparison morphism. -/
def of (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    DiagonalEqualizer ξ1 ξ2 w1 w2 where
  pullbackSpace := interpPullback ξ1 ξ2 w1 w2
  space := interpSpace ξ1 ξ2 w1 w2
  toV := interpToV ξ1 ξ2 w1 w2
  spaceHom :=
    pullback.fst (pairHom ξ1 ξ2 w1 w2) (diagHom σ) ≫ leftHom ξ1 ξ2 w1 w2
  closed := interClosed ξ1 ξ2
  formal := interpFormal ξ1 ξ2
  toFormal := interpToFormal ξ1 ξ2
  factor := interpFactor ξ1 ξ2 w1 w2

variable {ξ1 ξ2 : Triple σ V}
  {w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx}
  {w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx}

/-- Restriction of a presheaf on `Over S` to schemes over `V`. -/
def restrictFormal (V : Over S) (F : (Over S)ᵒᵖ ⥤ Type u) :
    (Over V.left)ᵒᵖ ⥤ Type u :=
  baseChangePresheaf V.hom F

/-- Restriction of a morphism of presheaves on `Over S` to schemes over `V`. -/
def restrictHom (V : Over S) {F G : (Over S)ᵒᵖ ⥤ Type u} (α : F ⟶ G) :
    restrictFormal V F ⟶ restrictFormal V G :=
  Functor.whiskerLeft (Over.map V.hom).op α

/-- The stored fibre product is `V'_1 ×_V V'_2`. -/
theorem pullbackSpace_eq :
    (of ξ1 ξ2 w1 w2).pullbackSpace = pullback w1.toV w2.toV :=
  sorry

/-- The stored space is the diagonal pullback of the interpolating pair. -/
theorem space_eq :
    (of ξ1 ξ2 w1 w2).space = pullback (pairHom ξ1 ξ2 w1 w2) (diagHom σ) :=
  sorry

/-- The stored closed subset is the intersection `Z_1 ∩ Z_2`. -/
theorem closed_eq : (of ξ1 ξ2 w1 w2).closed = ξ1.Z ⊓ ξ2.Z :=
  sorry

/-- The stored formal equalizer is the functor equalizer of `leftHat` and
`rightHat`. -/
theorem formal_eq :
    (of ξ1 ξ2 w1 w2).formal = equalizer (leftHat ξ1 ξ2) (rightHat ξ1 ξ2) :=
  sorry

/-- The two composites `E' ⟶ V'_i ⟶ V` agree. -/
theorem toV_comp (D : DiagonalEqualizer ξ1 ξ2 w1 w2) :
    interpToV ξ1 ξ2 w1 w2 =
      pullback.fst (pairHom ξ1 ξ2 w1 w2) (diagHom σ) ≫
        pullback.snd w1.toV w2.toV ≫ w2.toV :=
  sorry

/-- Postcomposing `factor` with `toFormal` recovers the completion of `toV`. -/
theorem factor_comp_ι :
    (of ξ1 ξ2 w1 w2).factor ≫ (of ξ1 ξ2 w1 w2).toFormal =
      completionAlong.map (interpToV ξ1 ξ2 w1 w2) (interClosed ξ1 ξ2) :=
  sorry

/-- Completing `spaceHom` along `T'` sends the inverse image of `Z` into `T'`. -/
theorem spaceHom_mapsClosed (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Points.map (of ξ1 ξ2 w1 w2).spaceHom ''
        (((of ξ1 ξ2 w1 w2).closed.preimage
            (Points.continuous_map (of ξ1 ξ2 w1 w2).toV) : Closeds _) : Set _) ⊆
      (σ.T' : Set (Points σ.X')) :=
  sorry

/-- The completed interpolating map `E'_{/Z} ⟶ X'_{/T'}`. -/
def completionSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    completionAlong (of ξ1 ξ2 w1 w2).space
      ((of ξ1 ξ2 w1 w2).closed.preimage
        (Points.continuous_map (of ξ1 ξ2 w1 w2).toV)) ⟶
      σ.completion :=
  completionAlong.mapOfLe (of ξ1 ξ2 w1 w2).spaceHom
    ((of ξ1 ξ2 w1 w2).closed.preimage
      (Points.continuous_map (of ξ1 ξ2 w1 w2).toV))
    σ.T' (spaceHom_mapsClosed ξ1 ξ2 w1 w2)

/-- The structure morphism of `E_W` over `V`. -/
def toOver (D : DiagonalEqualizer ξ1 ξ2 w1 w2) : D.formal ⟶ (ofOver V).functorOfPoints :=
  D.toFormal ≫ completionAlong.ι (ofOver V) D.closed

/-- The open fibre product `E' ×_V (V \ Z)`. -/
def openPullback (D : DiagonalEqualizer ξ1 ξ2 w1 w2) : AlgebraicSpace S :=
  pullback D.toV (AlgebraicSpace.openComplementι (ofOver V) D.closed)

/-- The projection `E' ×_V (V \ Z) ⟶ V \ Z`. -/
def openPullbackSnd (D : DiagonalEqualizer ξ1 ξ2 w1 w2) : openPullback D ⟶
    openComplementAlong (ofOver V) D.closed :=
  pullback.snd D.toV (AlgebraicSpace.openComplementι (ofOver V) D.closed)

/-- `E' ⟶ V` is separated. -/
instance instSeparated_toV (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Separated (interpToV ξ1 ξ2 w1 w2) :=
  sorry

/-- `E' ⟶ V` is locally of finite type. -/
instance instLocallyOfFiniteType_toV (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    LocallyOfFiniteType (interpToV ξ1 ξ2 w1 w2) :=
  sorry

/-- `E'` is locally Noetherian. -/
instance instIsLocallyNoetherian_space (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    IsLocallyNoetherian (interpSpace ξ1 ξ2 w1 w2) :=
  sorry

/-- `E_W` is a formal algebraic space. -/
instance instIsFormal_formal (ξ1 ξ2 : Triple σ V) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (interpFormal ξ1 ξ2) :=
  sorry

/-- `E_W` is locally Noetherian. -/
instance instIsLocallyNoetherian_formal (ξ1 ξ2 : Triple σ V) :
    FormalAlgebraicSpace.IsLocallyNoetherian (interpFormal ξ1 ξ2) :=
  sorry

/-- The structure morphism of the canonical formal equalizer over `V`. -/
def interpToOver (ξ1 ξ2 : Triple σ V) :
    interpFormal ξ1 ξ2 ⟶ (ofOver V).functorOfPoints :=
  interpToFormal ξ1 ξ2 ≫ completionAlong.ι (ofOver V) (interClosed ξ1 ξ2)

/-- `E_W` is separated over `V`. -/
instance instSeparated_formal (ξ1 ξ2 : Triple σ V) :
    FormalAlgebraicSpace.Separated (interpToOver ξ1 ξ2) :=
  sorry

/-- The comparison `E'_{/Z} ⟶ E_W` is locally of finite type. -/
instance instLocallyOfFiniteType_factor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.LocallyOfFiniteType (interpFactor ξ1 ξ2 w1 w2) :=
  sorry

/-- The comparison `E'_{/Z} ⟶ E_W` is a formal modification. -/
instance instFormalModification_factor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.FormalModification (interpFactor ξ1 ξ2 w1 w2) :=
  sorry

/-- The restriction of `ξ1.u'` to `V \ (Z_1 ∪ Z_2)`. -/
def leftOpen (ξ1 ξ2 : Triple σ V) :
    openComplementAlong (ofOver V) (ξ1.Z ⊔ ξ2.Z) ⟶ σ.openComplement :=
  openComplementAlong.mapOfLe le_sup_left ≫ ξ1.u'

/-- The restriction of `ξ2.u'` to `V \ (Z_1 ∪ Z_2)`. -/
def rightOpen (ξ1 ξ2 : Triple σ V) :
    openComplementAlong (ofOver V) (ξ1.Z ⊔ ξ2.Z) ⟶ σ.openComplement :=
  openComplementAlong.mapOfLe le_sup_right ≫ ξ2.u'

/-- The underlying `V`-section of `E' ×_V (V \ Z)` lands in
`V \ (Z_1 ∪ Z_2)`. -/
theorem openRestrict_spec (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over S)ᵒᵖ}
    (x : (openPullback (of ξ1 ξ2 w1 w2)).functorOfPoints.obj U) :
    Set.range
        (Points.map
          (OpenSubspace.homOfPointsSection
            ((openPullbackSnd (of ξ1 ξ2 w1 w2)).app U x).1)) ⊆
      (AlgebraicSpace.openComplement (ofOver V) (ξ1.Z ⊔ ξ2.Z) : Set _) :=
  sorry

/-- The induced morphism `E' ×_V (V \ Z) ⟶ V \ (Z_1 ∪ Z_2)`. -/
def openRestrict (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    openPullback (of ξ1 ξ2 w1 w2) ⟶
      openComplementAlong (ofOver V) (ξ1.Z ⊔ ξ2.Z) where
  app U := ofHom fun x ↦
    ⟨(openPullbackSnd (of ξ1 ξ2 w1 w2)).app U x |>.1,
      openRestrict_spec ξ1 ξ2 w1 w2 x⟩
  naturality := sorry

/-- Postcomposing `openRestrict` with the inclusion of
`V \ (Z_1 ∪ Z_2)` into `V \ Z` recovers the projection to `V \ Z`. -/
theorem openRestrict_comp_mapOfLe (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    openRestrict ξ1 ξ2 w1 w2 ≫
        openComplementAlong.mapOfLe
          (inf_le_sup : ξ1.Z ⊓ ξ2.Z ≤ ξ1.Z ⊔ ξ2.Z) =
      openPullbackSnd (of ξ1 ξ2 w1 w2) :=
  sorry

/-- The algebraic space over `V` whose `T`-points are maps into `E'` over `V`. -/
def sliceSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    AlgebraicSpace V.left :=
  AlgebraicSpace.sliceSpace (of ξ1 ξ2 w1 w2).space (of ξ1 ξ2 w1 w2).toV

/-- `E'` over `V` is locally of finite type. -/
instance instLocallyOfFiniteType_sliceSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    LocallyOfFiniteType (toBase (sliceSpace ξ1 ξ2 w1 w2)) :=
  sorry

/-- `E'` over `V` is locally Noetherian. -/
instance instIsLocallyNoetherian_sliceSpace (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    IsLocallyNoetherian (sliceSpace ξ1 ξ2 w1 w2) :=
  sorry

/-- The inverse image `(E' ⟶ V)⁻¹ Z` as a closed subset of `E'` over `V`. -/
def sliceClosed (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    Closeds (Points (sliceSpace ξ1 ξ2 w1 w2)) :=
  ((of ξ1 ξ2 w1 w2).closed.preimage
      (Points.continuous_map (of ξ1 ξ2 w1 w2).toV)).preimage
    (continuous_pointsSlice (of ξ1 ξ2 w1 w2).space (of ξ1 ξ2 w1 w2).toV)

/-- The fibre of `E_W` over `V`. -/
def sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (Over V.left)ᵒᵖ ⥤ Type u :=
  formalSlicePresheaf (of ξ1 ξ2 w1 w2).formal (toOver (of ξ1 ξ2 w1 w2))

/-- The fibre of `E_W` over `V` is a formal algebraic space. -/
instance instIsFormal_sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (sliceFormal ξ1 ξ2 w1 w2) :=
  sorry

/-- The fibre of `E_W` over `V` is locally Noetherian. -/
instance instIsLocallyNoetherian_sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.IsLocallyNoetherian (sliceFormal ξ1 ξ2 w1 w2) :=
  sorry

/-- Completing a slice section along `(E' ⟶ V)⁻¹ Z` yields a completion of
`E'` along the inverse image of `Z`. -/
theorem sliceFactor_mapsInto (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over V.left)ᵒᵖ}
    (x : (completionAlong (sliceSpace ξ1 ξ2 w1 w2)
      (sliceClosed ξ1 ξ2 w1 w2)).obj U) :
    mapsInto
      (((of ξ1 ξ2 w1 w2).closed.preimage
          (Points.continuous_map (of ξ1 ξ2 w1 w2).toV) : Closeds _) : Set _)
      (x.1).1 :=
  sorry

/-- The image of `sliceFactor` in `E_W` lies over the structure morphism of
`T`. -/
theorem sliceFactor_liesOver (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over V.left)ᵒᵖ}
    (x : (completionAlong (sliceSpace ξ1 ξ2 w1 w2)
      (sliceClosed ξ1 ξ2 w1 w2)).obj U) :
    (toOver (of ξ1 ξ2 w1 w2)).app (op ((Over.map V.hom).obj U.unop))
        ((of ξ1 ξ2 w1 w2).factor.app (op ((Over.map V.hom).obj U.unop))
          ⟨(x.1).1, sliceFactor_mapsInto ξ1 ξ2 w1 w2 x⟩) =
      yonedaEquiv (ofOverMap (overHom V U.unop)) :=
  sorry

/-- The restriction of `E'_{/Z} ⟶ E_W` to schemes over `V`. -/
def sliceFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    completionAlong (sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2) ⟶
      sliceFormal ξ1 ξ2 w1 w2 where
  app U := ofHom fun x ↦
    ⟨(of ξ1 ξ2 w1 w2).factor.app (op ((Over.map V.hom).obj U.unop))
        ⟨(x.1).1, sliceFactor_mapsInto ξ1 ξ2 w1 w2 x⟩,
      sliceFactor_liesOver ξ1 ξ2 w1 w2 x⟩
  naturality := sorry

/-- Completing the reduced equalizer image along `Z` equalizes `leftHat` and
`rightHat`. -/
theorem fromReduced_equalizes (ξ1 ξ2 : Triple σ V) :
    (completionAlong.fromReduced (hatEqualizerClosed ξ1 ξ2) ≫
          completionAlong.mapOfLe (𝟙 (ofOver V)) (hatEqualizerClosed ξ1 ξ2)
            (interClosed ξ1 ξ2) (hatEqualizerClosed_subset ξ1 ξ2)) ≫
        leftHat ξ1 ξ2 =
      (completionAlong.fromReduced (hatEqualizerClosed ξ1 ξ2) ≫
          completionAlong.mapOfLe (𝟙 (ofOver V)) (hatEqualizerClosed ξ1 ξ2)
            (interClosed ξ1 ξ2) (hatEqualizerClosed_subset ξ1 ξ2)) ≫
        rightHat ξ1 ξ2 :=
  sorry

/-- The reduced induced structure on the image of `equalizer.ι`, as a morphism
into `E_W`. -/
def fromReducedToFormal (ξ1 ξ2 : Triple σ V) :
    (ClosedSubspaceStructure.reduced (hatEqualizerClosed ξ1 ξ2)).space.functorOfPoints ⟶
      interpFormal ξ1 ξ2 :=
  equalizer.lift
    (completionAlong.fromReduced (hatEqualizerClosed ξ1 ξ2) ≫
      completionAlong.mapOfLe (𝟙 (ofOver V)) (hatEqualizerClosed ξ1 ξ2)
        (interClosed ξ1 ξ2) (hatEqualizerClosed_subset ξ1 ξ2))
    (fromReduced_equalizes ξ1 ξ2)

/-- Postcomposing `fromReducedToFormal` with `equalizer.ι` recovers the
restriction of `fromReduced` of `Z`. -/
theorem fromReducedToFormal_comp_ι (ξ1 ξ2 : Triple σ V) :
    fromReducedToFormal ξ1 ξ2 ≫ interpToFormal ξ1 ξ2 =
      completionAlong.fromReduced (hatEqualizerClosed ξ1 ξ2) ≫
        completionAlong.mapOfLe (𝟙 (ofOver V)) (hatEqualizerClosed ξ1 ξ2)
          (interClosed ξ1 ξ2) (hatEqualizerClosed_subset ξ1 ξ2) :=
  sorry

/-- The reduction of the fibre of `E_W` over `V`, as the reduced induced closed
subspace of the image of `equalizer.ι`, sliced over `V`. -/
def sliceFormalReductionSpace (ξ1 ξ2 : Triple σ V) : AlgebraicSpace V.left :=
  AlgebraicSpace.sliceSpace
    (ClosedSubspaceStructure.reduced (hatEqualizerClosed ξ1 ξ2)).space
    (ClosedSubspaceStructure.reduced (hatEqualizerClosed ξ1 ξ2)).ι

/-- The algebraic space of `sliceFormalReductionSpace` is the slice of the
reduced equalizer image. -/
theorem sliceFormalReductionSpace_eq (ξ1 ξ2 : Triple σ V) :
    sliceFormalReductionSpace ξ1 ξ2 =
      AlgebraicSpace.sliceSpace
        (ClosedSubspaceStructure.reduced (hatEqualizerClosed ξ1 ξ2)).space
        (ClosedSubspaceStructure.reduced (hatEqualizerClosed ξ1 ξ2)).ι :=
  sorry

/-- The image of the sliced reduced equalizer inclusion in `E_W` lies over the
structure morphism of `T`. -/
theorem sliceFormalReduction_liesOver (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    {U : (Over V.left)ᵒᵖ}
    (x : (sliceFormalReductionSpace ξ1 ξ2).functorOfPoints.obj U) :
    (toOver (of ξ1 ξ2 w1 w2)).app (op ((Over.map V.hom).obj U.unop))
        ((fromReducedToFormal ξ1 ξ2).app (op ((Over.map V.hom).obj U.unop)) x.1) =
      yonedaEquiv (ofOverMap (overHom V U.unop)) :=
  sorry

/-- The restriction of `fromReduced` of `Z` into the fibre of `E_W` over `V`. -/
def sliceFormalReductionι (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (sliceFormalReductionSpace ξ1 ξ2).functorOfPoints ⟶
      sliceFormal ξ1 ξ2 w1 w2 where
  app U := ofHom fun x ↦
    ⟨(fromReducedToFormal ξ1 ξ2).app (op ((Over.map V.hom).obj U.unop)) x.1,
      sliceFormalReduction_liesOver ξ1 ξ2 w1 w2 x⟩
  naturality := sorry

/-- Components of `sliceFormalReductionι` are the sliced `fromReducedToFormal`
sections. -/
theorem sliceFormalReductionι_app (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx)
    (U : (Over V.left)ᵒᵖ)
    (x : (sliceFormalReductionSpace ξ1 ξ2).functorOfPoints.obj U) :
    ((sliceFormalReductionι ξ1 ξ2 w1 w2).app U x).1 =
      (fromReducedToFormal ξ1 ξ2).app (op ((Over.map V.hom).obj U.unop)) x.1 :=
  sorry

/-- The reduction of the fibre of `E_W` over `V` is the reduced induced closed
subspace of the image of `equalizer.ι`. -/
instance instReduction_sliceFormal (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.Reduction (sliceFormal ξ1 ξ2 w1 w2) where
  space := sliceFormalReductionSpace ξ1 ξ2
  ι := sliceFormalReductionι ξ1 ξ2 w1 w2
  isReduced := sorry
  representable := sorry
  isThickening := sorry
  liftUnique := sorry

/-- The reduction of the fibre of `E_W` is locally of finite type over `V`. -/
instance instLocallyOfFiniteType_sliceReduction (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    LocallyOfFiniteType
      (toBase (FormalAlgebraicSpace.reduction (sliceFormal ξ1 ξ2 w1 w2))) :=
  sorry

/-- The comparison over `V` is locally of finite type. -/
instance instLocallyOfFiniteType_sliceFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.LocallyOfFiniteType (sliceFactor ξ1 ξ2 w1 w2) :=
  sorry

/-- The comparison over `V` is a formal modification. -/
instance instFormalModification_sliceFactor (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    FormalAlgebraicSpace.FormalModification (sliceFactor ξ1 ξ2 w1 w2) :=
  sorry

/-- The contraction situation over `V` with algebraic space `E'` over `V`,
closed subset `(E' ⟶ V)⁻¹ Z`, formal algebraic space the fibre of `E_W`, and
comparison the restriction of `factor`. -/
def toSituation (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    ContractionSituation V.left :=
  ContractionSituation.of (sliceSpace ξ1 ξ2 w1 w2) (sliceClosed ξ1 ξ2 w1 w2)
    (sliceFormal ξ1 ξ2 w1 w2) (sliceFactor ξ1 ξ2 w1 w2)

/-- The algebraic space of `toSituation` is `E'` viewed over `V`. -/
theorem toSituation_X' (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).X' = sliceSpace ξ1 ξ2 w1 w2 :=
  sorry

/-- The closed subset of `toSituation` is `(E' ⟶ V)⁻¹ Z`. -/
theorem toSituation_T' (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).T' = sliceClosed ξ1 ξ2 w1 w2 :=
  sorry

/-- The formal algebraic space of `toSituation` is the fibre of `E_W` over
`V`. -/
theorem toSituation_W (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).W = sliceFormal ξ1 ξ2 w1 w2 :=
  sorry

/-- The comparison of `toSituation` is the restriction of `factor`. -/
theorem toSituation_g (ξ1 ξ2 : Triple σ V)
    (w1 : CompatibilityWitness σ V ξ1.Z ξ1.u' ξ1.hatx)
    (w2 : CompatibilityWitness σ V ξ2.Z ξ2.u' ξ2.hatx) :
    (toSituation ξ1 ξ2 w1 w2).g = sliceFactor ξ1 ξ2 w1 w2 :=
  sorry

/-- The two triples restrict to the same element of `F(A)` along `φ : A ⟶ V`. -/
def agrees (ξ1 ξ2 : Triple σ V) {A : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian A.left] (φ : A ⟶ V) : Prop :=
  Triple.map φ ξ1 = Triple.map φ ξ2

/-- Agreement of the two triples is stable under precomposition over `V`. -/
theorem agrees_restrict (ξ1 ξ2 : Triple σ V) {A B : Over V.left}
    [AlgebraicGeometry.IsLocallyNoetherian A.left]
    [AlgebraicGeometry.IsLocallyNoetherian B.left]
    (φ : B ⟶ A) (h : agrees ξ1 ξ2 (overHom V A)) :
    agrees ξ1 ξ2 (overHom V B) :=
  sorry

/-- The functor on locally Noetherian schemes over `V` sending `φ` to the
proposition `Triple.map φ ξ1 = Triple.map φ ξ2`. -/
def agreesFunctor (ξ1 ξ2 : Triple σ V) :
    (locallyNoetherian V.left).FullSubcategoryᵒᵖ ⥤ Type (u + 1) where
  obj A := ULift.{u + 1} (PLift (agrees ξ1 ξ2 (overHom V A.unop.obj)))
  map φ := ofHom fun x ↦
    ⟨⟨agrees_restrict ξ1 ξ2 φ.unop.hom x.down.down⟩⟩
  map_id := sorry
  map_comp := sorry

/-- Components of `agreesFunctor` are `PLift` of agreement of the restricted
triples. -/
theorem agreesFunctor_obj (ξ1 ξ2 : Triple σ V)
    (A : (locallyNoetherian V.left).FullSubcategory) :
    (agreesFunctor ξ1 ξ2).obj (op A) =
      ULift.{u + 1} (PLift (agrees ξ1 ξ2 (overHom V A.obj))) :=
  sorry

end DiagonalEqualizer

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
