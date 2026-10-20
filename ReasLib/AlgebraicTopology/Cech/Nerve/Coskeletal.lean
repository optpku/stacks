/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.Cech.Nerve.Projection
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmentation
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Coskeletal
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018I

# Coskeletality of Cech nerves

Maps into a Cech nerve are classified by a single degree-zero map satisfying the two-face
compatibility condition.  These data form a presheaf on simplicial objects and vary functorially
with the underlying arrow.  A fixed Cech nerve represents its classifier presheaf; under uniform
existence the pointwise representations assemble into a Yoneda isomorphism.  The classification
is exposed independently of its consequence that every Cech nerve is `1`-coskeletal.
-/

@[expose] public section

open CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]
variable (f : Arrow C)

namespace cechNerve

/-- A degree-zero map into the left object of `f` whose composites with the two faces agree after
composition with `f`. -/
@[stacks 018I "compatible degree-zero Cech-nerve datum"]
abbrev CompatibleZeroSimplex (V : SimplicialObject C) :=
  { g0 : V _⦋0⦌ ⟶ f.left //
    V.δ 0 ≫ g0 ≫ f.hom = V.δ 1 ≫ g0 ≫ f.hom }

namespace CompatibleZeroSimplex

/-- Regard a compatible Cech-nerve zero-simplex as the compatible degree-zero datum for the
augmentation obtained by composing with the underlying arrow. -/
@[stacks 018I "compatible Cech datum induces augmentation data"]
def toAugmentation {V : SimplicialObject C} (e : CompatibleZeroSimplex f V) :
    SimplicialObject.Augmentation.Compatible V f.right :=
  ⟨e.1 ≫ f.hom, e.2⟩

/-- The degree-zero map underlying `toAugmentation` is composition with the Cech arrow. -/
@[simp, stacks 018I "underlying augmentation datum of a compatible Cech datum"]
theorem toAugmentation.val {V : SimplicialObject C} (e : CompatibleZeroSimplex f V) :
    (toAugmentation f e).1 = e.1 ≫ f.hom := sorry

/-- Pulling back compatible degree-zero data along a simplicial map preserves the two-face
condition. -/
@[stacks 018I "pullback preserves compatible Cech data"]
theorem pullback.condition {V W : SimplicialObject C} (α : V ⟶ W)
    (e : CompatibleZeroSimplex f W) :
    V.δ 0 ≫ (α.app (op ⦋0⦌) ≫ e.1) ≫ f.hom =
      V.δ 1 ≫ (α.app (op ⦋0⦌) ≫ e.1) ≫ f.hom := sorry

/-- Pull back compatible degree-zero data along a simplicial map. -/
@[stacks 018I "pullback of compatible Cech data"]
def pullback {V W : SimplicialObject C} (α : V ⟶ W) :
    CompatibleZeroSimplex f W ⟶ CompatibleZeroSimplex f V :=
  ↾(fun e ↦ ⟨α.app (op ⦋0⦌) ≫ e.1, pullback.condition f α e⟩)

/-- The underlying degree-zero map of pulled-back compatible data. -/
@[simp, stacks 018I "underlying map of pulled-back compatible Cech data"] theorem pullback.val {V W : SimplicialObject C} (α : V ⟶ W)
    (e : CompatibleZeroSimplex f W) :
    (pullback f α e).1 = α.app (op ⦋0⦌) ≫ e.1 := sorry

/-- Pullback of compatible degree-zero data along an identity is the identity morphism. -/
@[simp, stacks 018I "identity pullback of compatible Cech data"] theorem pullback.id {V : SimplicialObject C} :
    pullback f (𝟙 V) = 𝟙 (CompatibleZeroSimplex f V) := sorry

/-- Pullback of compatible degree-zero data reverses composition. -/
@[simp, stacks 018I "composition of compatible Cech pullbacks"] theorem pullback.comp {U V W : SimplicialObject C}
    (α : U ⟶ V) (β : V ⟶ W) :
    pullback f (α ≫ β) = pullback f β ≫ pullback f α := sorry

/-- Mapping compatible data along a square preserves the two-face condition. -/
@[stacks 018I "map preserves compatible Cech data"]
theorem map.condition {f g : Arrow C} (F : f ⟶ g) {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) :
    V.δ 0 ≫ (e.1 ≫ F.left) ≫ g.hom =
      V.δ 1 ≫ (e.1 ≫ F.left) ≫ g.hom := sorry

/-- A commutative square maps compatible degree-zero data along its left component. -/
@[stacks 018I "map of compatible Cech data"]
def map {f g : Arrow C} (F : f ⟶ g) {V : SimplicialObject C} :
    CompatibleZeroSimplex f V ⟶ CompatibleZeroSimplex g V :=
  ↾(fun e ↦ ⟨e.1 ≫ F.left, map.condition F e⟩)

/-- The underlying degree-zero map after applying a commutative square. -/
@[simp, stacks 018I "underlying map of mapped compatible Cech data"] theorem map.val {f g : Arrow C} (F : f ⟶ g) {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) :
    (map F e).1 = e.1 ≫ F.left := sorry

/-- The identity square acts identically on compatible degree-zero data. -/
@[simp, stacks 018I "identity map of compatible Cech data"] theorem map.id (f : Arrow C) {V : SimplicialObject C} :
    map (V := V) (𝟙 f) = 𝟙 (CompatibleZeroSimplex f V) := sorry

/-- Mapping compatible degree-zero data respects composition of squares. -/
@[simp, stacks 018I "composition of compatible Cech maps"] theorem map.comp {f g h : Arrow C} (F : f ⟶ g) (G : g ⟶ h)
    {V : SimplicialObject C} :
    map (V := V) (F ≫ G) =
      map (V := V) F ≫ map (V := V) G := sorry

/-- Pullback in the simplicial object commutes with mapping along a square of arrows. -/
@[stacks 018I "interchange of Cech data pullback and map"]
theorem interchange {f g : Arrow C} (F : f ⟶ g) {V W : SimplicialObject C}
    (α : V ⟶ W) :
    pullback f α ≫ map (V := V) F =
      map (V := W) F ≫ pullback g α := sorry

end CompatibleZeroSimplex

namespace zeroSimplex

/-- Compatible degree-zero data for `f`, contravariantly functorial in the source simplicial
object. -/
@[stacks 018I "compatible zero-simplex classifier presheaf"]
def presheaf : (SimplicialObject C)ᵒᵖ ⥤ Type v where
  obj V := CompatibleZeroSimplex f V.unop
  map α := CompatibleZeroSimplex.pullback f α.unop
  map_id V := CompatibleZeroSimplex.pullback.id f (V := V.unop)
  map_comp α β := CompatibleZeroSimplex.pullback.comp f β.unop α.unop

namespace presheaf

/-- A square of arrows induces the natural map between their compatible-zero-simplex
presheaves. -/
@[stacks 018I "functoriality of the compatible zero-simplex classifier"]
def map {f g : Arrow C} (F : f ⟶ g) : presheaf f ⟶ presheaf g where
  app _ := CompatibleZeroSimplex.map F
  naturality _ _ α := CompatibleZeroSimplex.interchange F α.unop

/-- Pointwise, the map of classifier presheaves postcomposes the degree-zero map with the left
side of the square. -/
@[simp, stacks 018I "pointwise compatible Cech classifier map"] theorem map.app_apply {f g : Arrow C} (F : f ⟶ g)
    (V : (SimplicialObject C)ᵒᵖ) (e : (presheaf f).obj V) :
    ((map F).app V e).1 = e.1 ≫ F.left := sorry

/-- The identity square induces the identity map of classifier presheaves. -/
@[simp, stacks 018I "identity compatible Cech classifier map"] theorem map.id (f : Arrow C) : map (𝟙 f) = 𝟙 (presheaf f) := sorry

/-- Classifier-presheaf maps respect composition of commutative squares. -/
@[simp, stacks 018I "composition of compatible Cech classifier maps"] theorem map.comp {f g h : Arrow C} (F : f ⟶ g) (G : g ⟶ h) :
    map (F ≫ G) = map F ≫ map G := sorry

end presheaf

/-- The compatible-zero-simplex classifier, functorial in the target arrow. -/
@[stacks 018I "compatible zero-simplex classifier functor"]
def functor : Arrow C ⥤ ((SimplicialObject C)ᵒᵖ ⥤ Type v) where
  obj := presheaf
  map := presheaf.map
  map_id := presheaf.map.id
  map_comp := presheaf.map.comp

end zeroSimplex

variable [f.HasCechNerve]

/-- The degree-zero component of a map into a Cech nerve satisfies the two-face compatibility
condition after composition with the underlying arrow. -/
@[stacks 018I "degree-zero compatibility for maps into a Cech nerve"]
theorem zeroSimplex.condition {V : SimplicialObject C}
    (g : V ⟶ f.cechNerve) :
    V.δ 0 ≫ (g.app (op ⦋0⦌) ≫
      Arrow.cechNerve.π f (op ⦋0⦌) 0) ≫ f.hom =
      V.δ 1 ≫ (g.app (op ⦋0⦌) ≫
        Arrow.cechNerve.π f (op ⦋0⦌) 0) ≫ f.hom := sorry

/-- Extract the compatible degree-zero map from a morphism into a Cech nerve. -/
@[stacks 018I "degree-zero classifier for maps into a Cech nerve"]
def zeroSimplex {V : SimplicialObject C} (g : V ⟶ f.cechNerve) :
    CompatibleZeroSimplex f V :=
  ⟨g.app (op ⦋0⦌) ≫ Arrow.cechNerve.π f (op ⦋0⦌) 0,
    zeroSimplex.condition f g⟩

/-- The vertex maps defining the degreewise Cech-nerve classifier satisfy the wide-pullback
compatibility relation. -/
@[stacks 018I "Cech-nerve reconstruction compatibility"]
theorem zeroSimplex.lift.condition {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) :
    ∀ (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)),
      (V.map (SimplexCategory.const ⦋0⦌ n.unop i).op ≫ e.1) ≫ f.hom =
        (Augmentation.ofZeroSimplex (CompatibleZeroSimplex.toAugmentation f e)).app n := sorry

/-- The degreewise wide-pullback map reconstructed from a compatible degree-zero map. -/
@[stacks 018I "Cech-nerve reconstruction component"]
noncomputable def zeroSimplex.lift.component {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V)
    (n : SimplexCategoryᵒᵖ) :
    V.obj n ⟶ f.cechNerve.obj n :=
  Arrow.cechNerve.lift f n
    ((Augmentation.ofZeroSimplex (CompatibleZeroSimplex.toAugmentation f e)).app n)
    (fun i ↦ V.map (SimplexCategory.const ⦋0⦌ n.unop i).op ≫ e.1)
    (zeroSimplex.lift.condition f e n)

/-- The base projection of the reconstructed component is the augmentation classified by the
compatible Cech datum. -/
@[simp, stacks 018I "base projection of Cech-nerve reconstruction"]
theorem zeroSimplex.lift.component.base {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) (n : SimplexCategoryᵒᵖ) :
    zeroSimplex.lift.component f e n ≫
        Arrow.cechNerve.base f n =
      (Augmentation.ofZeroSimplex
        (CompatibleZeroSimplex.toAugmentation f e)).app n := sorry

/-- A vertex projection of the reconstructed component is the corresponding simplex vertex
followed by the compatible degree-zero map. -/
@[simp, stacks 018I "vertex projection of Cech-nerve reconstruction"]
theorem zeroSimplex.lift.component.π {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    zeroSimplex.lift.component f e n ≫
        Arrow.cechNerve.π f n i =
      V.map (SimplexCategory.const ⦋0⦌ n.unop i).op ≫ e.1 := sorry

/-- The reconstructed degreewise maps commute with simplex operators. -/
@[stacks 018I "Cech-nerve reconstruction naturality"]
theorem zeroSimplex.lift.naturality {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    V.map φ ≫ zeroSimplex.lift.component f e m =
      zeroSimplex.lift.component f e n ≫ f.cechNerve.map φ := sorry

/-- Construct a morphism into a Cech nerve from a compatible degree-zero map.  Its components are
the maps to the iterated pullbacks induced by all vertices of a simplex. -/
@[stacks 018I "constructing a map into a Cech nerve from degree zero"]
noncomputable def zeroSimplex.lift {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) :
    V ⟶ f.cechNerve where
  app n := zeroSimplex.lift.component f e n
  naturality _ _ φ := zeroSimplex.lift.naturality f e φ

/-- The component of the Cech-nerve map reconstructed from its compatible degree-zero datum. -/
@[simp, stacks 018I "Cech-nerve reconstruction component formula"]
theorem zeroSimplex.lift.app {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) (n : SimplexCategoryᵒᵖ) :
    (zeroSimplex.lift f e).app n = zeroSimplex.lift.component f e n := sorry

/-- Reconstructing a map into a Cech nerve from its degree-zero classifier gives the original
map. -/
@[stacks 018I "Cech-nerve reconstruction after classification"]
theorem zeroSimplex.homEquiv.left_inv {V : SimplicialObject C}
    (g : V ⟶ f.cechNerve) :
    zeroSimplex.lift f (zeroSimplex f g) = g := sorry

/-- Extracting degree zero from the reconstructed Cech-nerve map gives the prescribed datum. -/
@[stacks 018I "Cech-nerve reconstruction specification"]
theorem zeroSimplex.homEquiv.right_inv {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) :
    zeroSimplex f (zeroSimplex.lift f e) = e := sorry

/-- Lemma 14.20.3 (018I): morphisms into the Cech nerve of `f` are canonically classified by a
degree-zero map whose composites with the two faces agree after composition with `f`. -/
@[stacks 018I "classification of maps into a Cech nerve"]
noncomputable def zeroSimplex.homEquiv (V : SimplicialObject C) :
    (V ⟶ f.cechNerve) ≃
      CompatibleZeroSimplex f V where
  toFun := zeroSimplex f
  invFun := cechNerve.zeroSimplex.lift f
  left_inv := cechNerve.zeroSimplex.homEquiv.left_inv f
  right_inv := cechNerve.zeroSimplex.homEquiv.right_inv f

/-- The forward Cech-nerve classifier is degree-zero evaluation followed by the canonical
pullback projection. -/
@[simp, stacks 018I "Cech-nerve classifier forward formula"]
theorem zeroSimplex.homEquiv.apply {V : SimplicialObject C}
    (g : V ⟶ f.cechNerve) :
    zeroSimplex.homEquiv f V g = zeroSimplex f g := sorry

/-- The inverse Cech-nerve classifier reconstructs the map from its compatible degree-zero
datum. -/
@[simp, stacks 018I "Cech-nerve classifier inverse formula"]
theorem zeroSimplex.homEquiv.symm_apply {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) :
    (zeroSimplex.homEquiv f V).symm e = cechNerve.zeroSimplex.lift f e := sorry

/-- The inverse Cech-nerve classifier has the prescribed degree-zero projection. -/
@[simp, stacks 018I "Cech-nerve classifier inverse degree-zero formula"]
theorem zeroSimplex.homEquiv.symm_apply_zero {V : SimplicialObject C}
    (e : CompatibleZeroSimplex f V) :
    ((zeroSimplex.homEquiv f V).symm e).app (op ⦋0⦌) ≫
      Arrow.cechNerve.π f (op ⦋0⦌) 0 = e.1 := sorry

/-- Extracting degree zero after precomposition pulls the compatible datum back along the source
simplicial map. -/
@[simp, stacks 018I "source naturality of the degree-zero classifier"]
theorem zeroSimplex.comp {V W : SimplicialObject C} (α : V ⟶ W)
    (g : W ⟶ f.cechNerve) :
    zeroSimplex f (α ≫ g) =
      CompatibleZeroSimplex.pullback f α (zeroSimplex f g) := sorry

/-- Extracting degree zero after a map of Cech nerves maps the compatible datum along the
underlying square. -/
@[simp, stacks 018I "arrow naturality of the degree-zero classifier"]
theorem zeroSimplex.map {g : Arrow C} [g.HasCechNerve] (F : f ⟶ g)
    {V : SimplicialObject C} (h : V ⟶ f.cechNerve) :
    zeroSimplex g (h ≫ Arrow.mapCechNerve F) =
      CompatibleZeroSimplex.map F (zeroSimplex f h) := sorry

/-- The degree-zero classification is natural under precomposition in the source simplicial
object. -/
@[stacks 018I "source naturality of the Cech-nerve classifier"]
theorem zeroSimplex.homEquiv.comp {V W : SimplicialObject C} (α : V ⟶ W)
    (g : W ⟶ f.cechNerve) :
    zeroSimplex.homEquiv f V (α ≫ g) =
      (zeroSimplex.presheaf f).map α.op (zeroSimplex.homEquiv f W g) := sorry

/-- The classifier equivalence is natural under a commutative square between two arrows, using
only the Cech-nerve limits at its two endpoints. -/
@[stacks 018I "arrow naturality of the Cech-nerve classifier"]
theorem zeroSimplex.homEquiv.map {g : Arrow C} [g.HasCechNerve] (F : f ⟶ g)
    {V : SimplicialObject C} (h : V ⟶ f.cechNerve) :
    zeroSimplex.homEquiv g V (h ≫ Arrow.mapCechNerve F) =
      (zeroSimplex.presheaf.map F).app (op V) (zeroSimplex.homEquiv f V h) := sorry

/-- The Cech nerve of a fixed arrow represents its compatible-zero-simplex presheaf. -/
@[stacks 018I "Cech nerve represents the compatible zero-simplex classifier"]
noncomputable def zeroSimplex.representableBy :
    (zeroSimplex.presheaf f).RepresentableBy f.cechNerve where
  homEquiv := zeroSimplex.homEquiv f _
  homEquiv_comp := zeroSimplex.homEquiv.comp f

namespace zeroSimplex

section Uniform

variable [∀ g : Arrow C, g.HasCechNerve]

/-- Naturality in the arrow variable of the Yoneda isomorphisms supplied by the pointwise
Cech-nerve representations. -/
@[stacks 018I "naturality of Cech-nerve Yoneda representations"]
theorem yonedaIso.naturality {a b : Arrow C} (F : a ⟶ b) :
    (SimplicialObject.cechNerve ⋙ yoneda).map F ≫
        (representableBy b).toIso.hom =
      (representableBy a).toIso.hom ≫ presheaf.map F := sorry

/-- Under uniform existence of Cech nerves, the Yoneda image of the Cech-nerve functor is the
compatible-zero-simplex classifier functor. -/
@[stacks 018I "Yoneda classification of the Cech-nerve functor"]
noncomputable def yonedaIso :
    SimplicialObject.cechNerve ⋙ yoneda ≅ functor (C := C) :=
  NatIso.ofComponents
    (fun g ↦ (representableBy g).toIso)
    (fun {_ _} F ↦ yonedaIso.naturality F)

/-- The component of the uniform Yoneda classification is the isomorphism supplied by the
pointwise representability owner. -/
@[simp, stacks 018I "Cech-nerve Yoneda classification component"]
theorem yonedaIso_app (g : Arrow C) :
    (yonedaIso (C := C)).app g = (representableBy g).toIso := sorry

end Uniform

end zeroSimplex

/-- Lemma 14.20.3 (018I): the Cech nerve of any morphism is canonically `1`-coskeletal. -/
@[stacks 018I "Cech nerves are 1-coskeletal"]
instance isCoskeletalOne : f.cechNerve.IsCoskeletal 1 := sorry

namespace truncation

/-- Truncating at degree `1` gives a bijection from maps into a Cech nerve to maps between the
corresponding truncations. This is the Cech-nerve specialization of
`SimplicialObject.IsCoskeletal.truncation.map_bijective`. -/
@[stacks 018I "Cech-nerve morphisms are determined by 1-truncations"]
theorem map_bijective (V : SimplicialObject C) :
    Function.Bijective (fun g : V ⟶ f.cechNerve ↦
      (SimplicialObject.truncation 1).map g) := sorry

/-- Morphisms into a Cech nerve are determined exactly by their `1`-truncations. This thin
specialization uses only the coskeletality of this Cech nerve, not a global coskeleton functor. -/
@[stacks 018I "Cech-nerve morphisms from 1-truncations"]
noncomputable def homEquiv (V : SimplicialObject C) :
    (V ⟶ f.cechNerve) ≃
      ((SimplicialObject.truncation 1).obj V ⟶
        (SimplicialObject.truncation 1).obj f.cechNerve) :=
  SimplicialObject.IsCoskeletal.truncation.homEquiv f.cechNerve 1 V

/-- The forward truncation classifier sends a simplicial map to its `1`-truncation. -/
@[simp, stacks 018I "Cech-nerve truncation classifier formula"] theorem homEquiv.apply (V : SimplicialObject C)
    (g : V ⟶ f.cechNerve) :
    homEquiv f V g = (SimplicialObject.truncation 1).map g := sorry

/-- The inverse Cech-nerve truncation classifier is the canonical right-Kan lift into the
`1`-coskeletal target. -/
@[simp, stacks 018I "inverse Cech-nerve truncation classifier formula"]
theorem homEquiv.symm_apply (V : SimplicialObject C)
    (g : (SimplicialObject.truncation 1).obj V ⟶
      (SimplicialObject.truncation 1).obj f.cechNerve) :
    (homEquiv f V).symm g =
      f.cechNerve.liftOfIsRightKanExtension
        (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ f.cechNerve)) V g := sorry

end truncation

end cechNerve

end CategoryTheory.Arrow
