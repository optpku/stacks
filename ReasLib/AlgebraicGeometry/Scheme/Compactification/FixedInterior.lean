/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Category

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- The category of compactifications of the fixed scheme `X` over `S`. -/
abbrev Of (S : Scheme.{u}) (X : Over S) :=
  ObjectProperty.FullSubcategory
    (fun j : Under X ↦ Compactification.Is S (Arrow.mk j.hom))

namespace Of

/-- A fixed-interior compactification carries the general compactification property. -/
instance instIs (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    Compactification.Is S (Arrow.mk P.obj.hom) := P.property

/-- The interior map of a fixed-interior compactification is quasi-compact. -/
instance instQuasiCompact (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    QuasiCompact P.obj.hom.left := P.property.quasiCompact

/-- The ambient scheme of a fixed-interior compactification is proper over the base. -/
instance instIsProper (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    IsProper P.obj.right.hom := P.property.isProper

/-- Construct a fixed-interior compactification from its ambient scheme and interior map. -/
abbrev mk (S : Scheme.{u}) {X : Over S} (Xbar : Over S) (j : X ⟶ Xbar)
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsProper Xbar.hom] : Of S X :=
  ⟨Under.mk j,
    { isOpenImmersion := inferInstanceAs (IsOpenImmersion j.left)
      quasiCompact := inferInstanceAs (QuasiCompact j.left)
      isProper := inferInstanceAs (IsProper Xbar.hom) }⟩

/-- The interior immersion of a fixed-interior compactification. -/
def ι {S : Scheme.{u}} {X : Over S} (P : Of S X) : X.left ⟶ P.obj.right.left :=
  P.obj.hom.left

/-- The interior immersion of a fixed-interior compactification is an open immersion. -/
instance instIsOpenImmersion (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    IsOpenImmersion (ι P) := P.property.isOpenImmersion

/-- The constructed compactification has the specified interior immersion. -/
theorem mk_ι (S : Scheme.{u}) {X : Over S} (Xbar : Over S) (j : X ⟶ Xbar)
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsProper Xbar.hom] :
    ι (mk S Xbar j) = j.left := sorry

/-- Regard a fixed-interior compactification as a general compactification over `S`. -/
def toCompactification {S : Scheme.{u}} {X : Over S} (P : Of S X) :
    Compactification S :=
  ⟨Arrow.mk P.obj.hom, P.property⟩

/-- The general compactification underlying `P` has the expected arrow. -/
theorem toCompactification_obj {S : Scheme.{u}} {X : Over S} (P : Of S X) :
    (toCompactification P).obj = Arrow.mk P.obj.hom := sorry

/-- The map of ambient schemes underlying a morphism of fixed-interior compactifications. -/
def ambientMap {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (f : P ⟶ Q) :
    P.obj.right.left ⟶ Q.obj.right.left :=
  f.hom.right.left

/-- A morphism of fixed-interior compactifications commutes with the interior immersions. -/
theorem ι_comp_ambientMap {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (f : P ⟶ Q) :
    ι P ≫ ambientMap f = ι Q := sorry

end Of

/-- A fixed-interior compactification is dense when its interior is both topologically and
scheme-theoretically dense in its ambient scheme. -/
class IsDense (S : Scheme.{u}) (X : Over S) (P : Of S X) : Prop where
  /-- The interior immersion has dense image. -/
  isDominant : IsDominant (Of.ι P)
  /-- The open image of the interior is scheme-theoretically dense. -/
  schemeTheoreticallyDense : schemeTheoreticallyDense (Of.ι P).opensRange

namespace IsDense

/-- Density of a fixed-interior compactification exposes its topological and
scheme-theoretic conditions together. -/
theorem isDense_iff (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    IsDense S X P ↔
      DenseRange (Of.ι P) ∧
        AlgebraicGeometry.schemeTheoreticallyDense (Of.ι P).opensRange := sorry

/-- A dense fixed-interior compactification has a dominant interior immersion. -/
instance instIsDominant (S : Scheme.{u}) (X : Over S) (P : Of S X)
    [h : IsDense S X P] : IsDominant (Of.ι P) := h.isDominant

end IsDense

/-- The full subcategory of compactifications whose fixed interior is topologically and
scheme-theoretically dense. -/
abbrev DenseOf (S : Scheme.{u}) (X : Over S) :=
  ObjectProperty.FullSubcategory (IsDense S X)

namespace DenseOf

/-- A bundled dense compactification carries its defining density property. -/
instance instIsDense (S : Scheme.{u}) (X : Over S) (P : DenseOf S X) :
    IsDense S X P.obj := P.property

/-- The inclusion of dense fixed-interior compactifications into all compactifications. -/
def inclusion (S : Scheme.{u}) (X : Over S) : DenseOf S X ⥤ Of S X :=
  ObjectProperty.ι (IsDense S X)

/-- The dense-compactification inclusion forgets only the density property. -/
theorem inclusion_obj (S : Scheme.{u}) (X : Over S) (P : DenseOf S X) :
    (inclusion S X).obj P = P.obj := sorry

end DenseOf

namespace Of

/-- A quasi-compact, scheme-theoretically dominant open immersion has
scheme-theoretically dense open image. -/
theorem schemeTheoreticallyDense_of_isSchemeTheoreticallyDominant
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] : schemeTheoreticallyDense j.opensRange := by
  have hker : j.opensRange.ι.ker = ⊥ := by
    rw [← j.isoOpensRange_inv_comp, Scheme.Hom.ker_comp_of_isIso]
    exact j.ker_eq_bot
  have : QuasiCompact j.opensRange.ι := by
    rw [← j.isoOpensRange_inv_comp]
    infer_instance
  intro V
  apply Scheme.IdealSheafData.ext
  funext W
  change (Y.homOfLE (inf_le_right : j.opensRange ⊓ V ≤ V)).ker.ideal W = _
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion j.opensRange.ι
    (Y.homOfLE (inf_le_right : j.opensRange ⊓ V ≤ V))
    (Y.homOfLE (inf_le_left : j.opensRange ⊓ V ≤ j.opensRange)) V.ι
    (isPullback_opens_inf j.opensRange V).flip W, hker]
  apply Ideal.comap_bot_of_injective
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- The scheme-theoretic image of a quasi-compact immersion into a proper scheme is a
dense compactification, with its canonical map to the given proper scheme. -/
private theorem exists_dense_of_immersion (S : Scheme.{u}) {X : Over S}
    (Y : Over S) (j : X ⟶ Y) [IsImmersion j.left] [QuasiCompact j.left]
    [IsProper Y.hom] :
    ∃ (P : Of S X), IsDense S X P ∧
      ∃ (f : P.obj.right ⟶ Y), P.obj.hom ≫ f = j := by
  have : IsSchemeTheoreticallyDominant j.left.toImage := by
    constructor
    apply Scheme.IdealSheafData.ext
    funext U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
    apply (RingHom.injective_iff_ker_eq_bot _).mp
    exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
      (F := j.left.image.sheaf) j.left.toImage.c U.1
      (fun x _ ↦ j.left.stalkFunctor_toImage_injective x)
  let Y' : Over S := Over.mk (j.left.imageι ≫ Y.hom)
  let j' : X ⟶ Y' := by
    refine Over.homMk (w := ?_) j.left.toImage
    change j.left.toImage ≫ j.left.imageι ≫ Y.hom = X.hom
    rw [← Category.assoc, j.left.toImage_imageι]
    exact Over.w j
  letI : IsOpenImmersion j'.left := by
    change IsOpenImmersion j.left.toImage
    infer_instance
  letI : QuasiCompact j'.left := by
    change QuasiCompact j.left.toImage
    infer_instance
  letI : IsProper Y'.hom := by
    change IsProper (j.left.imageι ≫ Y.hom)
    infer_instance
  let P : Of S X := mk S Y' j'
  let f : P.obj.right ⟶ Y := by
    change Y' ⟶ Y
    refine Over.homMk (w := ?_) j.left.imageι
    rfl
  refine ⟨P, ⟨inferInstanceAs (IsDominant j.left.toImage), ?_⟩, f, ?_⟩
  · change schemeTheoreticallyDense j.left.toImage.opensRange
    exact schemeTheoreticallyDense_of_isSchemeTheoreticallyDominant j.left.toImage
  · apply Over.OverMorphism.ext
    change j.left.toImage ≫ j.left.imageι = j.left
    exact j.left.toImage_imageι

/-- Over a quasi-compact quasi-separated base, fixed-interior compactifications of a
compactifiable scheme form a cofiltered category. -/
instance instIsCofiltered (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (X : Over S) [Nonempty (Of S X)] : IsCofiltered (Of S X) where
  cone_objs P Q := by
    let Y : Over S := Over.mk
      (Limits.pullback.fst P.obj.right.hom Q.obj.right.hom ≫ P.obj.right.hom)
    let p : Y ⟶ P.obj.right := Over.homMk (w := by rfl)
      (Limits.pullback.fst _ _)
    let q : Y ⟶ Q.obj.right := Over.homMk (w := by
      exact Limits.pullback.condition.symm) (Limits.pullback.snd _ _)
    have hPQ : ι P ≫ P.obj.right.hom = ι Q ≫ Q.obj.right.hom := by
      change P.obj.hom.left ≫ P.obj.right.hom = Q.obj.hom.left ≫ Q.obj.right.hom
      exact (Over.w P.obj.hom).trans (Over.w Q.obj.hom).symm
    let j : X ⟶ Y := Over.homMk
      (Limits.pullback.lift (ι P) (ι Q) hPQ)
      (by
        change Limits.pullback.lift P.ι Q.ι _ ≫
          Limits.pullback.fst _ _ ≫ P.obj.right.hom = X.hom
        rw [← Category.assoc, Limits.pullback.lift_fst]
        exact Over.w P.obj.hom)
    have hjp : j ≫ p = P.obj.hom := by
      apply Over.OverMorphism.ext
      change Limits.pullback.lift P.ι Q.ι _ ≫ Limits.pullback.fst _ _ = P.obj.hom.left
      rw [Limits.pullback.lift_fst]
      rfl
    have hjq : j ≫ q = Q.obj.hom := by
      apply Over.OverMorphism.ext
      change Limits.pullback.lift P.ι Q.ι _ ≫ Limits.pullback.snd _ _ = Q.obj.hom.left
      rw [Limits.pullback.lift_snd]
      rfl
    have hPopen : IsOpenImmersion P.ι := inferInstance
    letI : IsOpenImmersion P.obj.hom.left := hPopen
    letI : IsOpenImmersion Q.obj.hom.left := by
      change IsOpenImmersion (Of.ι Q)
      infer_instance
    letI : IsProper p.left := by
      change IsProper (Limits.pullback.fst P.obj.right.hom Q.obj.right.hom)
      infer_instance
    letI : IsProper Y.hom := by
      change IsProper (Limits.pullback.fst P.obj.right.hom Q.obj.right.hom ≫ P.obj.right.hom)
      infer_instance
    have : IsImmersion (j.left ≫ p.left) := by
      rw [← Over.comp_left, hjp]
      infer_instance
    have : IsImmersion j.left := IsImmersion.of_comp _ p.left
    have : QuasiCompact (j.left ≫ p.left) := by
      rw [← Over.comp_left, hjp]
      infer_instance
    have : QuasiCompact j.left := QuasiCompact.of_comp _ p.left
    obtain ⟨R, _, r, hr⟩ := exists_dense_of_immersion S Y j
    exact ⟨R, ObjectProperty.homMk (Under.homMk (r ≫ p) (by
      rw [← Category.assoc, hr, hjp])),
      ObjectProperty.homMk (Under.homMk (r ≫ q) (by
        rw [← Category.assoc, hr, hjq])), trivial⟩
  cone_maps {P Q} f g := by
    let Y := Limits.equalizer f.hom.right g.hom.right
    let e : Y ⟶ P.obj.right := Limits.equalizer.ι _ _
    letI : IsOpenImmersion P.obj.hom.left := by
      change IsOpenImmersion (ι P)
      infer_instance
    letI : IsProper Y.hom := by
      rw [← Over.w e]
      infer_instance
    let j : X ⟶ Y := Limits.equalizer.lift P.obj.hom
      ((Under.w f.hom).trans (Under.w g.hom).symm)
    have hje : j ≫ e = P.obj.hom := Limits.equalizer.lift_ι _ _
    have : IsImmersion (j.left ≫ e.left) := by
      rw [← Over.comp_left, hje]
      infer_instance
    have : IsImmersion j.left := IsImmersion.of_comp _ e.left
    have : QuasiCompact (j.left ≫ e.left) := by
      rw [← Over.comp_left, hje]
      infer_instance
    have : QuasiCompact j.left := QuasiCompact.of_comp _ e.left
    obtain ⟨R, _, r, hr⟩ := exists_dense_of_immersion S Y j
    refine ⟨R, ObjectProperty.homMk (Under.homMk (r ≫ e) (by
      rw [← Category.assoc, hr, hje])), ?_⟩
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    change (r ≫ e) ≫ f.hom.right = (r ≫ e) ≫ g.hom.right
    rw [Category.assoc, Category.assoc, Limits.equalizer.condition]

end Of

namespace DenseOf

/-- Compactifications with topologically and scheme-theoretically dense fixed interior form
an initial full subcategory of all fixed-interior compactifications. -/
instance instInitialInclusion (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] (X : Over S) [Nonempty (Of S X)] :
    Functor.Initial (inclusion S X) := by
  change Functor.Initial (ObjectProperty.ι (IsDense S X))
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro P
  letI : IsOpenImmersion P.obj.hom.left := by
    exact Of.instIsOpenImmersion S X P
  letI : QuasiCompact P.obj.hom.left := by
    exact Of.instQuasiCompact S X P
  obtain ⟨Q, hQ, f, hf⟩ := Of.exists_dense_of_immersion S P.obj.right P.obj.hom
  exact ⟨⟨Q, hQ⟩, ⟨ObjectProperty.homMk (Under.homMk f hf)⟩⟩

end DenseOf

namespace Of

/-- A morphism of fixed-interior compactifications with dense source interior pulls the open
image of the target interior back to the open image of the source interior. -/
theorem preimage_opensRange (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (X : Over S) [Nonempty (Of S X)] {P' P : Of S X} (f : P' ⟶ P)
    [IsDominant (ι P')] :
    ambientMap f ⁻¹ᵁ (ι P).opensRange = (ι P').opensRange := sorry

end Of


namespace Of

/-- The scheme-theoretic image factorization, bundled as a dense compactification.
Its ambient scheme and interior map are `j.left.image` and `j.left.toImage`.
No compactification is selected from an existence assertion. -/
noncomputable def denseImage (S : Scheme.{u}) {X : Over S}
    (Y : Over S) (j : X ⟶ Y) [IsImmersion j.left] [QuasiCompact j.left]
    [IsProper Y.hom] : DenseOf S X := by
  let Y' : Over S := Over.mk (j.left.imageι ≫ Y.hom)
  let j' : X ⟶ Y' := Over.homMk j.left.toImage (by
    change j.left.toImage ≫ j.left.imageι ≫ Y.hom = X.hom
    rw [← Category.assoc, j.left.toImage_imageι]
    exact Over.w j)
  letI : IsOpenImmersion j'.left := by
    change IsOpenImmersion j.left.toImage
    infer_instance
  letI : QuasiCompact j'.left := by
    change QuasiCompact j.left.toImage
    infer_instance
  letI : IsProper Y'.hom := by
    change IsProper (j.left.imageι ≫ Y.hom)
    infer_instance
  letI : IsSchemeTheoreticallyDominant j.left.toImage := by
    constructor
    apply Scheme.IdealSheafData.ext
    funext U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
    apply (RingHom.injective_iff_ker_eq_bot _).mp
    exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
      (F := j.left.image.sheaf) j.left.toImage.c U.1
      (fun x _ ↦ j.left.stalkFunctor_toImage_injective x)
  refine ⟨mk S Y' j', ⟨inferInstanceAs (IsDominant j.left.toImage), ?_⟩⟩
  change schemeTheoreticallyDense j.left.toImage.opensRange
  exact schemeTheoreticallyDense_of_isSchemeTheoreticallyDominant j.left.toImage

/-- The image factorization has its specified ambient scheme. -/
theorem denseImage_ambient (S : Scheme.{u}) {X : Over S}
    (Y : Over S) (j : X ⟶ Y) [IsImmersion j.left] [QuasiCompact j.left]
    [IsProper Y.hom] : (denseImage S Y j).obj.obj.right.left = j.left.image := rfl

/-- The image factorization has its specified open interior. -/
theorem denseImage_interior (S : Scheme.{u}) {X : Over S}
    (Y : Over S) (j : X ⟶ Y) [IsImmersion j.left] [QuasiCompact j.left]
    [IsProper Y.hom] : ι (denseImage S Y j).obj = j.left.toImage := rfl

/-- The canonical closed immersion from the image to its original ambient scheme. -/
noncomputable def denseImageToAmbient (S : Scheme.{u}) {X : Over S}
    (Y : Over S) (j : X ⟶ Y) [IsImmersion j.left] [QuasiCompact j.left]
    [IsProper Y.hom] : (denseImage S Y j).obj.obj.right ⟶ Y :=
  Over.homMk j.left.imageι (by rfl)

@[reassoc]
theorem denseImage_factorization (S : Scheme.{u}) {X : Over S}
    (Y : Over S) (j : X ⟶ Y) [IsImmersion j.left] [QuasiCompact j.left]
    [IsProper Y.hom] :
    (denseImage S Y j).obj.obj.hom ≫ denseImageToAmbient S Y j = j := by
  apply Over.OverMorphism.ext
  exact j.left.toImage_imageι

/-- The ambient fiber product used for a common refinement. -/
noncomputable def commonProduct {S : Scheme.{u}} {X : Over S} (P Q : Of S X) : Over S :=
  Over.mk (Limits.pullback.fst P.obj.right.hom Q.obj.right.hom ≫ P.obj.right.hom)

/-- The first projection from the ambient fiber product. -/
noncomputable def commonProductFst {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    commonProduct P Q ⟶ P.obj.right := Over.homMk (Limits.pullback.fst _ _) (by rfl)

/-- The second projection from the ambient fiber product. -/
noncomputable def commonProductSnd {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    commonProduct P Q ⟶ Q.obj.right :=
  Over.homMk (Limits.pullback.snd _ _) Limits.pullback.condition.symm

/-- The two interior immersions agree over their common base. -/
theorem interiorDiagonal_condition {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    ι P ≫ P.obj.right.hom = ι Q ≫ Q.obj.right.hom := by
  change P.obj.hom.left ≫ P.obj.right.hom = Q.obj.hom.left ≫ Q.obj.right.hom
  exact (Over.w P.obj.hom).trans (Over.w Q.obj.hom).symm

/-- The actual interior diagonal into the two ambient schemes' fiber product. -/
noncomputable def interiorDiagonal {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    X ⟶ commonProduct P Q :=
  Over.homMk (Limits.pullback.lift (ι P) (ι Q) (interiorDiagonal_condition P Q)) (by
    change Limits.pullback.lift (ι P) (ι Q) _ ≫
      Limits.pullback.fst _ _ ≫ P.obj.right.hom = X.hom
    rw [← Category.assoc, Limits.pullback.lift_fst]
    exact Over.w P.obj.hom)

@[reassoc]
theorem interiorDiagonal_fst {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    interiorDiagonal P Q ≫ commonProductFst P Q = P.obj.hom := by
  apply Over.OverMorphism.ext
  change Limits.pullback.lift (ι P) (ι Q) _ ≫ Limits.pullback.fst _ _ = P.obj.hom.left
  rw [Limits.pullback.lift_fst]
  rfl

@[reassoc]
theorem interiorDiagonal_snd {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    interiorDiagonal P Q ≫ commonProductSnd P Q = Q.obj.hom := by
  apply Over.OverMorphism.ext
  change Limits.pullback.lift (ι P) (ι Q) _ ≫ Limits.pullback.snd _ _ = Q.obj.hom.left
  rw [Limits.pullback.lift_snd]
  rfl

instance commonProduct_isProper {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    IsProper (commonProduct P Q).hom := by
  change IsProper (Limits.pullback.fst P.obj.right.hom Q.obj.right.hom ≫ P.obj.right.hom)
  infer_instance

instance interiorDiagonal_isImmersion {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    IsImmersion (interiorDiagonal P Q).left := by
  letI : IsOpenImmersion P.obj.hom.left := P.property.isOpenImmersion
  have : IsImmersion ((interiorDiagonal P Q).left ≫ (commonProductFst P Q).left) := by
    rw [← Over.comp_left, interiorDiagonal_fst]
    infer_instance
  exact IsImmersion.of_comp _ (commonProductFst P Q).left

instance interiorDiagonal_quasiCompact {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    QuasiCompact (interiorDiagonal P Q).left := by
  have : QuasiCompact ((interiorDiagonal P Q).left ≫ (commonProductFst P Q).left) := by
    rw [← Over.comp_left, interiorDiagonal_fst]
    exact P.property.quasiCompact
  letI : IsProper (commonProductFst P Q).left := by
    change IsProper (Limits.pullback.fst P.obj.right.hom Q.obj.right.hom)
    infer_instance
  exact QuasiCompact.of_comp _ (commonProductFst P Q).left

/-- The canonical dense common refinement: the scheme-theoretic closure of the
interior diagonal in the ambient fiber product. This uses the actual given `P` and `Q`,
with no nonemptiness, cofilteredness, or initiality choice. -/
noncomputable def commonRefinement {S : Scheme.{u}} {X : Over S} (P Q : Of S X) : DenseOf S X :=
  denseImage S (commonProduct P Q) (interiorDiagonal P Q)

/-- The closed image inclusion of the canonical refinement in the fiber product. -/
noncomputable def commonRefinementToProduct {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    (commonRefinement P Q).obj.obj.right ⟶ commonProduct P Q :=
  denseImageToAmbient S (commonProduct P Q) (interiorDiagonal P Q)

@[reassoc]
theorem commonRefinement_factorization {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    (commonRefinement P Q).obj.obj.hom ≫ commonRefinementToProduct P Q =
      interiorDiagonal P Q :=
  denseImage_factorization S (commonProduct P Q) (interiorDiagonal P Q)

/-- The first actual morphism of compactifications from the canonical common refinement. -/
noncomputable def commonRefinementFst {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    (commonRefinement P Q).obj ⟶ P :=
  ObjectProperty.homMk (Under.homMk
    (commonRefinementToProduct P Q ≫ commonProductFst P Q) (by
      rw [← Category.assoc, commonRefinement_factorization, interiorDiagonal_fst]))

/-- The second actual morphism of compactifications from the canonical common refinement. -/
noncomputable def commonRefinementSnd {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    (commonRefinement P Q).obj ⟶ Q :=
  ObjectProperty.homMk (Under.homMk
    (commonRefinementToProduct P Q ≫ commonProductSnd P Q) (by
      rw [← Category.assoc, commonRefinement_factorization, interiorDiagonal_snd]))

/-- The refinement's underlying scheme is exactly the diagonal's scheme-theoretic image. -/
theorem commonRefinement_ambient {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    (commonRefinement P Q).obj.obj.right.left = (interiorDiagonal P Q).left.image := rfl

/-- The refinement's interior map is the canonical map to that image. -/
theorem commonRefinement_interior {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    ι (commonRefinement P Q).obj = (interiorDiagonal P Q).left.toImage := rfl

/-- The image inclusion is a closed immersion, proved by the native image construction. -/
instance commonRefinementToProduct_isClosedImmersion
    {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    IsClosedImmersion (commonRefinementToProduct P Q).left := by
  change IsClosedImmersion (interiorDiagonal P Q).left.imageι
  infer_instance

/-- The first ambient map is the image inclusion followed by the first projection. -/
theorem commonRefinementFst_ambientMap {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    ambientMap (commonRefinementFst P Q) =
      (interiorDiagonal P Q).left.imageι ≫ Limits.pullback.fst _ _ := rfl

/-- The second ambient map is the image inclusion followed by the second projection. -/
theorem commonRefinementSnd_ambientMap {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    ambientMap (commonRefinementSnd P Q) =
      (interiorDiagonal P Q).left.imageι ≫ Limits.pullback.snd _ _ := rfl

instance commonRefinementFst_isProper {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    IsProper (ambientMap (commonRefinementFst P Q)) := by
  have : IsProper (ambientMap (commonRefinementFst P Q) ≫ P.obj.right.hom) := by
    change IsProper ((commonRefinementFst P Q).hom.right.left ≫ P.obj.right.hom)
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp _ P.obj.right.hom

instance commonRefinementSnd_isProper {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    IsProper (ambientMap (commonRefinementSnd P Q)) := by
  have : IsProper (ambientMap (commonRefinementSnd P Q) ≫ Q.obj.right.hom) := by
    change IsProper ((commonRefinementSnd P Q).hom.right.left ≫ Q.obj.right.hom)
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp _ Q.obj.right.hom

@[reassoc]
theorem commonRefinementFst_interior {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    ι (commonRefinement P Q).obj ≫ ambientMap (commonRefinementFst P Q) = ι P :=
  congrArg (fun f ↦ f.left) (Under.w (commonRefinementFst P Q).hom)

@[reassoc]
theorem commonRefinementSnd_interior {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    ι (commonRefinement P Q).obj ≫ ambientMap (commonRefinementSnd P Q) = ι Q :=
  congrArg (fun f ↦ f.left) (Under.w (commonRefinementSnd P Q).hom)

/-- Restricting the constructed interior map to any open of the interior is literal
composition with its open inclusion; no compactification is chosen again. -/
noncomputable def commonRefinementOnOpen {S : Scheme.{u}} {X : Over S}
    (P Q : Of S X) (U : X.left.Opens) : U.toScheme ⟶ (commonRefinement P Q).obj.obj.right.left :=
  U.ι ≫ ι (commonRefinement P Q).obj

@[reassoc]
theorem commonRefinementOnOpen_fst {S : Scheme.{u}} {X : Over S}
    (P Q : Of S X) (U : X.left.Opens) :
    commonRefinementOnOpen P Q U ≫ ambientMap (commonRefinementFst P Q) = U.ι ≫ ι P := by
  rw [commonRefinementOnOpen, Category.assoc, commonRefinementFst_interior]

@[reassoc]
theorem commonRefinementOnOpen_snd {S : Scheme.{u}} {X : Over S}
    (P Q : Of S X) (U : X.left.Opens) :
    commonRefinementOnOpen P Q U ≫ ambientMap (commonRefinementSnd P Q) = U.ι ≫ ι Q := by
  rw [commonRefinementOnOpen, Category.assoc, commonRefinementSnd_interior]

/-- These interior maps commute with every further open restriction. -/
@[reassoc]
theorem commonRefinementOnOpen_restrict {S : Scheme.{u}} {X : Over S}
    (P Q : Of S X) {U W : X.left.Opens} (h : W ≤ U) :
    X.left.homOfLE h ≫ commonRefinementOnOpen P Q U = commonRefinementOnOpen P Q W := by
  simp [commonRefinementOnOpen, ← Category.assoc]


/-- A commuting map of the original ambient schemes induces the corresponding map of
scheme-theoretic images. The actual map is the native map of closed subschemes. -/
noncomputable def denseImageMap (S : Scheme.{u}) {X : Over S}
    {Y Z : Over S} (j : X ⟶ Y) (k : X ⟶ Z)
    [IsImmersion j.left] [QuasiCompact j.left] [IsProper Y.hom]
    [IsImmersion k.left] [QuasiCompact k.left] [IsProper Z.hom]
    (f : Y ⟶ Z) (h : j ≫ f = k) : (denseImage S Y j).obj ⟶ (denseImage S Z k).obj := by
  have hleft : j.left ≫ f.left = k.left := congrArg (fun t ↦ t.left) h
  have hker : k.left.ker ≤ j.left.ker.map f.left := by
    rw [← Scheme.Hom.ker_comp, hleft]
  let m := Scheme.IdealSheafData.subschemeMap j.left.ker k.left.ker f.left hker
  have hm : m ≫ k.left.imageι = j.left.imageι ≫ f.left :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  refine ObjectProperty.homMk (Under.homMk (Over.homMk m ?_) ?_)
  · change m ≫ (k.left.imageι ≫ Z.hom) = j.left.imageι ≫ Y.hom
    rw [← Category.assoc, hm, Category.assoc, Over.w f]
  · apply Over.OverMorphism.ext
    change j.left.toImage ≫ m = k.left.toImage
    rw [← cancel_mono k.left.imageι, Category.assoc, hm, ← Category.assoc,
      j.left.toImage_imageι, k.left.toImage_imageι, hleft]

@[reassoc]
theorem denseImageMap_imageι (S : Scheme.{u}) {X : Over S}
    {Y Z : Over S} (j : X ⟶ Y) (k : X ⟶ Z)
    [IsImmersion j.left] [QuasiCompact j.left] [IsProper Y.hom]
    [IsImmersion k.left] [QuasiCompact k.left] [IsProper Z.hom]
    (f : Y ⟶ Z) (h : j ≫ f = k) :
    ambientMap (denseImageMap S j k f h) ≫ k.left.imageι = j.left.imageι ≫ f.left := by
  dsimp only [denseImageMap, ambientMap]
  exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ (by
    rw [← Scheme.Hom.ker_comp, ← Over.comp_left, h])

/-- The map of fiber products induced by two actual compactification morphisms. -/
noncomputable def commonProductMap {S : Scheme.{u}} {X : Over S}
    {P Q P' Q' : Of S X} (f : P ⟶ P') (g : Q ⟶ Q') :
    commonProduct P Q ⟶ commonProduct P' Q' :=
  Over.homMk
    (Limits.pullback.map P.obj.right.hom Q.obj.right.hom P'.obj.right.hom Q'.obj.right.hom
      (ambientMap f) (ambientMap g) (𝟙 S)
      (by
        change P.obj.right.hom ≫ 𝟙 S = f.hom.right.left ≫ P'.obj.right.hom
        rw [Category.comp_id]
        exact (Over.w f.hom.right).symm)
      (by
        change Q.obj.right.hom ≫ 𝟙 S = g.hom.right.left ≫ Q'.obj.right.hom
        rw [Category.comp_id]
        exact (Over.w g.hom.right).symm)) (by
    change Limits.pullback.map _ _ _ _ _ _ _ _ _ ≫
      Limits.pullback.fst _ _ ≫ P'.obj.right.hom =
        Limits.pullback.fst _ _ ≫ P.obj.right.hom
    rw [← Category.assoc, Limits.pullback.lift_fst, Category.assoc]
    exact congrArg (fun t ↦ Limits.pullback.fst P.obj.right.hom Q.obj.right.hom ≫ t)
      (Over.w f.hom.right))

/-- The product map preserves the common fixed interior. -/
theorem interiorDiagonal_map {S : Scheme.{u}} {X : Over S}
    {P Q P' Q' : Of S X} (f : P ⟶ P') (g : Q ⟶ Q') :
    interiorDiagonal P Q ≫ commonProductMap f g = interiorDiagonal P' Q' := by
  have hf : ι P ≫ ambientMap f = ι P' :=
    congrArg (fun t ↦ t.left) (Under.w f.hom)
  have hg : ι Q ≫ ambientMap g = ι Q' :=
    congrArg (fun t ↦ t.left) (Under.w g.hom)
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · change (Limits.pullback.lift (ι P) (ι Q) _ ≫
      Limits.pullback.lift
        (Limits.pullback.fst P.obj.right.hom Q.obj.right.hom ≫ ambientMap f)
        (Limits.pullback.snd P.obj.right.hom Q.obj.right.hom ≫ ambientMap g) _) ≫
        Limits.pullback.fst P'.obj.right.hom Q'.obj.right.hom =
      Limits.pullback.lift (ι P') (ι Q') _ ≫ Limits.pullback.fst _ _
    rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc,
      Limits.pullback.lift_fst]
    exact hf
  · change (Limits.pullback.lift (ι P) (ι Q) _ ≫
      Limits.pullback.lift
        (Limits.pullback.fst P.obj.right.hom Q.obj.right.hom ≫ ambientMap f)
        (Limits.pullback.snd P.obj.right.hom Q.obj.right.hom ≫ ambientMap g) _) ≫
        Limits.pullback.snd P'.obj.right.hom Q'.obj.right.hom =
      Limits.pullback.lift (ι P') (ι Q') _ ≫ Limits.pullback.snd _ _
    rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc,
      Limits.pullback.lift_snd]
    exact hg

theorem commonProductMap_id {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    commonProductMap (𝟙 P) (𝟙 Q) = 𝟙 (commonProduct P Q) := by
  apply Over.OverMorphism.ext
  change Limits.pullback.map P.obj.right.hom Q.obj.right.hom
    P.obj.right.hom Q.obj.right.hom (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _
  exact Limits.pullback.map_id

/-- Functorial comparison between the two explicitly constructed common refinements.
Both source and target are computed from the given pairs of compactifications. -/
noncomputable def commonRefinementMap {S : Scheme.{u}} {X : Over S}
    {P Q P' Q' : Of S X} (f : P ⟶ P') (g : Q ⟶ Q') :
    (commonRefinement P Q).obj ⟶ (commonRefinement P' Q').obj :=
  denseImageMap S (interiorDiagonal P Q) (interiorDiagonal P' Q')
    (commonProductMap f g) (interiorDiagonal_map f g)

/-- The comparison is anchored to the actual map of ambient fiber products. -/
@[reassoc]
theorem commonRefinementMap_imageι {S : Scheme.{u}} {X : Over S}
    {P Q P' Q' : Of S X} (f : P ⟶ P') (g : Q ⟶ Q') :
    ambientMap (commonRefinementMap f g) ≫ (interiorDiagonal P' Q').left.imageι =
      (interiorDiagonal P Q).left.imageι ≫ (commonProductMap f g).left :=
  denseImageMap_imageι S _ _ _ _

/-- Identity maps induce the identity on the explicit common refinement. -/
theorem commonRefinementMap_id {S : Scheme.{u}} {X : Over S} (P Q : Of S X) :
    commonRefinementMap (𝟙 P) (𝟙 Q) = 𝟙 (commonRefinement P Q).obj := by
  apply ObjectProperty.hom_ext
  apply Under.UnderMorphism.ext
  apply Over.OverMorphism.ext
  change ambientMap (commonRefinementMap (𝟙 P) (𝟙 Q)) = 𝟙 _
  apply (cancel_mono (commonRefinementToProduct P Q).left).1
  change ambientMap (commonRefinementMap (𝟙 P) (𝟙 Q)) ≫
      (interiorDiagonal P Q).left.imageι = 𝟙 _ ≫ (interiorDiagonal P Q).left.imageι
  rw [commonRefinementMap_imageι, Category.id_comp]
  rw [commonProductMap_id]
  exact Category.comp_id _

end Of

end AlgebraicGeometry.Scheme.Compactification
