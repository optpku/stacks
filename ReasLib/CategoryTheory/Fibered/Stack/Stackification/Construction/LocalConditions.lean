module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.Assembly
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.LocalEquivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Local models of the completed stack

Each completed object is compared on its stored cover with its stored local
objects. Hom preimages in the completion use the original prestack descent
preimage on the representative's actual cover.
-/

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology
open scoped CategoryTheory.Bicategory

noncomputable section

universe u v uF vF uX vX

namespace CategoryTheory.Functor.StackificationConstruction.DescentCompletion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF})

/-- A local model is compared to the restricted datum on its actual pullback cover. -/
def localComparisonRaw {U : C} (a : Object J F U) (I : a.cover.Arrow) :
    RawHom J F (ofObject J F (a.datum.obj I)) (pullbackObject J F I.f a) where
  cover := a.cover.pullback I.f
  left := le_top
  right := le_rfl
  arrow :=
    { hom L := a.datum.hom (L.f ≫ I.f) (i₁ := I) (i₂ := L.base)
        L.f (𝟙 L.Y) rfl (Category.id_comp _)
        ≫ (F.mapId (.mk (op L.Y))).hom.toNatTrans.app (a.datum.obj L.base)
      comm := by sorry }

/-- The reverse local comparison uses the reverse original descent arrow. -/
def localComparisonInverseRaw {U : C} (a : Object J F U) (I : a.cover.Arrow) :
    RawHom J F (pullbackObject J F I.f a) (ofObject J F (a.datum.obj I)) where
  cover := a.cover.pullback I.f
  left := le_rfl
  right := le_top
  arrow :=
    { hom L := (F.mapId (.mk (op L.Y))).inv.toNatTrans.app (a.datum.obj L.base)
        ≫ a.datum.hom (L.f ≫ I.f) (i₁ := L.base) (i₂ := I)
          (𝟙 L.Y) L.f (Category.id_comp _) rfl
      comm := by sorry }

/-- The stored local object and the restricted completion are explicitly isomorphic. -/
def localComparisonIso {U : C} (a : Object J F U) (I : a.cover.Arrow) :
    ofObject J F (a.datum.obj I) ≅ pullbackObject J F I.f a where
  hom := _root_.Quotient.mk'' (localComparisonRaw J F a I)
  inv := _root_.Quotient.mk'' (localComparisonInverseRaw J F a I)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The arrows stored by an actual cover form a covering family. -/
theorem coverArrows_mem {U : C} (R : J.Cover U) :
    Sieve.ofArrows (fun I : R.Arrow ↦ I.Y) (fun I ↦ I.f) ∈ J U :=
  J.superset_covering
    (fun V f hf ↦ Sieve.ofArrows_mk _ _ (⟨V, f, hf⟩ : R.Arrow)) R.2

/-- A representative between maximal-cover objects is an original descent morphism. -/
def unitRepresentativeDatum {U : C} {x y : F.obj (.mk (op U))}
    (φ : RawHom J F (ofObject J F x) (ofObject J F y)) :
    (F.toDescentData (fun I : φ.cover.Arrow ↦ I.f)).obj x ⟶
      (F.toDescentData (fun I : φ.cover.Arrow ↦ I.f)).obj y where
  hom I := φ.arrow.hom I
  comm := by sorry

/-- The original prestack supplies the actual global preimage of the stored
descent morphism, on the representative's original cover. -/
def unitPreimage (hF : F.IsPrestack J) {U : C} {x y : F.obj (.mk (op U))}
    (φ : (unitFunctor J F U).obj x ⟶ (unitFunctor J F U).obj y) : x ⟶ y := by
  letI := hF
  let raw := Quotient.out φ
  exact (F.fullyFaithfulToDescentData (fun I : raw.cover.Arrow ↦ I.f)
    (coverArrows_mem J raw.cover)).preimage (unitRepresentativeDatum J F raw)

/-- The unit on a prestack has actual inverse functions on Hom types. -/
def unitFullyFaithful (hF : F.IsPrestack J) (U : C) : (unitFunctor J F U).FullyFaithful where
  preimage := unitPreimage J F hF
  map_preimage := sorry
  preimage_map := sorry

end CategoryTheory.Functor.StackificationConstruction.DescentCompletion

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)

/-- A stored local fibre object is an actual original object over that same base. -/
def originalModel {U : C} (a : DescentCompletion.Object J (localFibers J p χ) U)
    (I : a.cover.Arrow) : p.Fiber I.Y :=
  ⟨(a.datum.obj I).1.obj.obj, (a.datum.obj I).2⟩

/-- Both representations have the same original object and maximal-cover
datum, after transporting its stored fibre-index equality. -/
theorem originalModel_image {U : C}
    (a : DescentCompletion.Object J (localFibers J p χ) U) (I : a.cover.Arrow) :
    ((comparison J p χ).fiberFunctor I.Y).obj (originalModel J p χ a I) =
      (Pseudofunctor.CoGrothendieck.standardFiber
        (completedPresheaf J p χ).toPseudofunctor' I.Y).obj
          (DescentCompletion.ofObject J (localFibers J p χ) (a.datum.obj I)) := sorry

/-- The local model's image is compared to the native chosen restriction by
the explicit local descent isomorphism and two actual Cartesian factors. -/
def modelComparisonIso {U : C}
    (a : DescentCompletion.Object J (localFibers J p χ) U) (I : a.cover.Arrow) :
    ((comparison J p χ).fiberFunctor I.Y).obj (originalModel J p χ a I) ≅
      I.f⁎[Functor.Cleavage.ofIsFibered (targetProjection J p χ)]
        ((Pseudofunctor.CoGrothendieck.standardFiber
          (completedPresheaf J p χ).toPseudofunctor' U).obj a) :=
  eqToIso (originalModel_image J p χ a I) ≪≫
  (Pseudofunctor.CoGrothendieck.standardFiber
    (completedPresheaf J p χ).toPseudofunctor' I.Y).mapIso
      (DescentCompletion.localComparisonIso J (localFibers J p χ) a I) ≪≫
    Pseudofunctor.CoGrothendieck.restrictionIso
      (completedPresheaf J p χ).toPseudofunctor' I.f a

/-- Every target object is locally in the image on its own stored cover,
with its stored original local models and explicit comparison isomorphisms. -/
theorem comparisonLocallyEssentiallySurjective [p.IsFibered] :
    CartesianBasedFunctor.LocallyEssentiallySurjective J (comparison J p χ) := by
  intro U y
  rcases y with ⟨⟨V, a⟩, h⟩
  change V = U at h
  subst U
  apply J.superset_covering (S := (a.cover : Sieve V)) _ a.cover.2
  intro W f hf
  let I : a.cover.Arrow := ⟨W, f, hf⟩
  exact ⟨originalModel J p χ a I, ⟨modelComparisonIso J p χ a I⟩⟩

/-- The comparison of an original fibre object is its maximal-cover local datum. -/
theorem comparisonFiber_image {V : C} (x : p.Fiber V) :
    ((comparison J p χ).fiberFunctor V).obj x =
      (Pseudofunctor.CoGrothendieck.standardFiber
        (completedPresheaf J p χ).toPseudofunctor' V).obj
        (DescentCompletion.ofObject J (localFibers J p χ)
          (((Localized.comparison J p χ).fiberFunctor V).obj x)) := sorry

/-- Recover an actual local-arrow fibre morphism from a completed comparison
morphism, through native realization fullness and original prestack descent. -/
def localizedPreimage {V : C} (x y : p.Fiber V)
    (τ : ((comparison J p χ).fiberFunctor V).obj x ⟶
      ((comparison J p χ).fiberFunctor V).obj y) :
    ((Localized.comparison J p χ).fiberFunctor V).obj x ⟶
      ((Localized.comparison J p χ).fiberFunctor V).obj y := by
  let F := (completedPresheaf J p χ).toPseudofunctor'
  let realized := eqToHom (comparisonFiber_image J p χ x).symm ≫ τ ≫
    eqToHom (comparisonFiber_image J p χ y)
  let original := (Functor.FullyFaithful.ofFullyFaithful
    (Functor.Fiber.inducedFunctor (Pseudofunctor.CoGrothendieck.comp_const F V))).preimage realized
  exact DescentCompletion.unitPreimage J (localFibers J p χ)
    (Localized.isPrestack J p χ (localCleavage J p χ)) original

/-- A local-arrow morphism retains its native covering representative. -/
def homLocalRepresentative {V : C} {x y : p.Fiber V}
    (τ : ((Localized.comparison J p χ).fiberFunctor V).obj x ⟶
      ((Localized.comparison J p χ).fiberFunctor V).obj y) :
    LocalArrow J p χ (⟨x.1⟩ : Separated J p χ) (⟨y.1⟩ : Separated J p χ) :=
  Quotient.out τ.1

/-- The representative cover is transported to the original common fibre index. -/
def homLocalCover {V : C} {x y : p.Fiber V}
    (τ : ((Localized.comparison J p χ).fiberFunctor V).obj x ⟶
      ((Localized.comparison J p χ).fiberFunctor V).obj y) : J.Cover V :=
  (homLocalRepresentative J p χ τ).cover.pullback (eqToHom x.2.symm)

/-- Endpoint transport identifies the two original selected source lifts. -/
theorem homLocalSource_eq {V : C} {x y : p.Fiber V}
    (τ : ((Localized.comparison J p χ).fiberFunctor V).obj x ⟶
      ((Localized.comparison J p χ).fiberFunctor V).obj y)
    (I : (homLocalCover J p χ τ).Arrow) :
    (I.f⁎[χ] x).1 = sourceRestriction J p χ (⟨x.1⟩ : Separated J p χ) I.base.f := sorry

/-- The native original representative has its actual displayed restriction base. -/
theorem homLocalOriginal_isHomLift {V : C} {x y : p.Fiber V}
    (τ : ((Localized.comparison J p χ).fiberFunctor V).obj x ⟶
      ((Localized.comparison J p χ).fiberFunctor V).obj y)
    (I : (homLocalCover J p χ τ).Arrow) :
    p.IsHomLift I.f (Quotient.out ((homLocalRepresentative J p χ τ).component I.base)) := sorry

/-- Each local preimage is the actual original representative factored through
the actual target lift; its source uses only the stored endpoint transport. -/
def homLocalPreimage {V : C} {x y : p.Fiber V}
    (τ : ((Localized.comparison J p χ).fiberFunctor V).obj x ⟶
      ((Localized.comparison J p χ).fiberFunctor V).obj y)
    (I : (homLocalCover J p χ τ).Arrow) : I.f⁎[χ] x ⟶ I.f⁎[χ] y := by
  let raw := Quotient.out ((homLocalRepresentative J p χ τ).component I.base)
  let target := χ.reindexLift I.f y
  let factor := @Functor.IsStronglyCartesian.map C X _ _ p
    I.Y V target.source y.1 I.f target.hom target.isStronglyCartesian
    I.Y (sourceRestriction J p χ (⟨x.1⟩ : Separated J p χ) I.base.f)
    (𝟙 I.Y) I.f (Category.id_comp I.f).symm raw
    (homLocalOriginal_isHomLift J p χ τ I)
  exact ⟨eqToHom (homLocalSource_eq J p χ τ I) ≫ factor, by sorry⟩

/-- Local preimages may use any caller cleavage. Both changes of selected
lifts are implemented by actual native Cartesian factor maps. -/
def homLocalPreimageWith (ξ : p.Cleavage) {V : C} {x y : p.Fiber V}
    (τ : ((Localized.comparison J p χ).fiberFunctor V).obj x ⟶
      ((Localized.comparison J p χ).fiberFunctor V).obj y)
    (I : (homLocalCover J p χ τ).Arrow) : I.f⁎[ξ] x ⟶ I.f⁎[ξ] y := by
  let source := χ.reindexLift I.f x
  let selected := ξ.reindexLift I.f x
  let raw := Quotient.out ((homLocalRepresentative J p χ τ).component I.base)
  let target := ξ.reindexLift I.f y
  let sourceFactor := @Functor.IsStronglyCartesian.map C X _ _ p
    I.Y V source.source x.1 I.f source.hom source.isStronglyCartesian
    I.Y selected.source (𝟙 I.Y) I.f (Category.id_comp I.f).symm
    selected.hom selected.isStronglyCartesian.toIsHomLift
  let targetFactor := @Functor.IsStronglyCartesian.map C X _ _ p
    I.Y V target.source y.1 I.f target.hom target.isStronglyCartesian
    I.Y (sourceRestriction J p χ (⟨x.1⟩ : Separated J p χ) I.base.f)
    (𝟙 I.Y) I.f (Category.id_comp I.f).symm raw
    (homLocalOriginal_isHomLift J p χ τ I)
  exact ⟨sourceFactor ≫ eqToHom (homLocalSource_eq J p χ τ I) ≫ targetFactor, by sorry⟩

end CategoryTheory.Functor.StackificationConstruction
