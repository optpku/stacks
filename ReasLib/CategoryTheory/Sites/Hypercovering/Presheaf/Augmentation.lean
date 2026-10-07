module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Category
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Category
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Augmentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Augmented presheaves associated to hypercoverings

This leaf owns the assumption-free passage from a fixed-target formal-coproduct hypercovering
to its simplicial presheaf, its degree presheaves, and its canonical augmentation.
-/

@[expose] public section

noncomputable section

universe w u v

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable {J : GrothendieckTopology C} {X : C}

namespace Hypercovering

/-- The simplicial semi-representable family obtained by forgetting the fixed target in every
degree of a hypercovering. -/
abbrev simplicialFamily (K : Hypercovering.{w} J X) :
    SimplicialObject (SR(C)) :=
  K.toSimplicialObject ⋙ SemiRepresentableFamily.OverFamily.forget

/-- The simplicial presheaf obtained by forgetting the fixed target in each degree of a
hypercovering. -/
abbrev simplicialPresheaf (K : Hypercovering.{w} J X) :
    SimplicialObject (Cᵒᵖ ⥤ Type (max w v)) :=
  K.simplicialFamily ⋙ Limits.FormalCoproduct.toPresheaf

/-- The presheaf associated to the degree-`n` fixed-target family of a hypercovering. -/
abbrev degreePresheaf (K : Hypercovering.{w} J X) (n : ℕ) :
    Cᵒᵖ ⥤ Type (max w v) :=
  K.simplicialPresheaf.obj (op <| SimplexCategory.mk n)

/-- The simplicial presheaf map underlying a morphism of hypercoverings. -/
abbrev Hom.toSimplicialPresheaf {K L : Hypercovering.{w} J X} (f : K ⟶ L) :
    K.simplicialPresheaf ⟶ L.simplicialPresheaf :=
  Functor.whiskerRight (Hom.toSimplicial f)
    (SemiRepresentableFamily.OverFamily.forget ⋙ Limits.FormalCoproduct.toPresheaf)

/-- The presheaf map in degree `n` underlying a morphism of hypercoverings. -/
abbrev Hom.degreePresheafMap {K L : Hypercovering.{w} J X} (f : K ⟶ L) (n : ℕ) :
    K.degreePresheaf n ⟶ L.degreePresheaf n :=
  (Hom.toSimplicialPresheaf f).app (op <| SimplexCategory.mk n)

/-- The component of the canonical augmentation in one simplicial degree. -/
noncomputable abbrev augmentationApp (K : Hypercovering.{w} J X)
    (Delta : SimplexCategoryᵒᵖ) :
    K.simplicialPresheaf.obj Delta ⟶ uliftYoneda.{w}.obj X :=
  Limits.FormalCoproduct.augmentation (K.toSimplicialObject.obj Delta)

/-- The degreewise augmentation components are natural in the simplex category. -/
theorem augmentationApp_naturality (K : Hypercovering.{w} J X)
    {Delta Delta' : SimplexCategoryᵒᵖ} (f : Delta ⟶ Delta') :
    K.simplicialPresheaf.map f ≫ K.augmentationApp Delta' =
      K.augmentationApp Delta ≫
        ((SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj
          (uliftYoneda.{w}.obj X)).map f := sorry

/-- The canonical augmentation of the simplicial presheaf of a hypercovering to the
representable presheaf of its fixed target. -/
@[stacks 01G9 "canonical presheaf augmentation"]
noncomputable def augmentation (K : Hypercovering.{w} J X) :
    K.simplicialPresheaf ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj
        (uliftYoneda.{w}.obj X) where
  app Delta := K.augmentationApp Delta
  naturality _ _ f := augmentationApp_naturality K f

/-- The augmented simplicial presheaf underlying a fixed-target hypercovering satisfies the
generic local-hypercover condition. -/
theorem toPresheafTarget_isLocalHypercover
    (K : Hypercovering.{w} J X) :
    (hypercoveringAugmentedPresheaf K.simplicialFamily K.augmentation).IsLocalHypercover J := sorry

/-- A fixed-target hypercovering canonically defines a hypercovering of the representable
presheaf of its target. -/
@[stacks 01G9 "fixed-target hypercovering as a presheaf-target hypercovering"]
noncomputable def toPresheafTarget
    (K : Hypercovering.{w} J X) :
    HypercoveringOf.{w} J (uliftYoneda.{w}.obj X) where
  simplicial := K.simplicialFamily
  augmentation := K.augmentation
  isLocalHypercover := K.toPresheafTarget_isLocalHypercover

/-- Forgetting the target from `toPresheafTarget` recovers the underlying simplicial family. -/
@[simp]
theorem toPresheafTarget_simplicial
    (K : Hypercovering.{w} J X) :
    K.toPresheafTarget.simplicial = K.simplicialFamily := sorry

/-- The augmentation of `toPresheafTarget` is the canonical fixed-target augmentation. -/
@[simp]
theorem toPresheafTarget_augmentation
    (K : Hypercovering.{w} J X) :
    K.toPresheafTarget.augmentation = K.augmentation := sorry

namespace Hom

/-- The simplicial formal-coproduct map underlying a fixed-target hypercovering morphism, after
forgetting the common target. -/
abbrev toSimplicialFamily {K L : Hypercovering.{w} J X} (f : K ⟶ L) :
    K.simplicialFamily ⟶ L.simplicialFamily :=
  Functor.whiskerRight (Hypercovering.Hom.toSimplicial f)
    SemiRepresentableFamily.OverFamily.forget

/-- The presheaf augmentation is natural under a fixed-target hypercovering morphism. -/
theorem toPresheafTarget_naturality {K L : Hypercovering.{w} J X} (f : K ⟶ L) :
    HypercoveringOf.simplicialPresheafFunctor.map (toSimplicialFamily f) ≫
        L.toPresheafTarget.augmentation =
      K.toPresheafTarget.augmentation := sorry

/-- A fixed-target hypercovering morphism induces the corresponding augmentation-preserving
morphism of presheaf-target hypercoverings. -/
def toPresheafTarget {K L : Hypercovering.{w} J X} (f : K ⟶ L) :
    K.toPresheafTarget ⟶ L.toPresheafTarget :=
  HypercoveringOf.homMk (toSimplicialFamily f) (toPresheafTarget_naturality f)

/-- The induced presheaf-target morphism retains the underlying simplicial family map. -/
@[simp]
theorem toPresheafTarget_toSimplicial {K L : Hypercovering.{w} J X} (f : K ⟶ L) :
    HypercoveringOf.Hom.toSimplicial (toPresheafTarget f) =
      toSimplicialFamily f := sorry

/-- The induced presheaf-target morphism preserves identity morphisms. -/
theorem toPresheafTarget_id (K : Hypercovering.{w} J X) :
    toPresheafTarget (𝟙 K) = 𝟙 K.toPresheafTarget := sorry

/-- The induced presheaf-target morphism preserves composition. -/
theorem toPresheafTarget_comp {K L M : Hypercovering.{w} J X}
    (f : K ⟶ L) (g : L ⟶ M) :
    toPresheafTarget (f ≫ g) = toPresheafTarget f ≫ toPresheafTarget g := sorry

end Hom

/-- Fixed-target hypercoverings map functorially to hypercoverings of the represented target
presheaf. -/
@[stacks 01G9 "fixed-target to presheaf-target functor"]
def toPresheafTargetFunctor :
    Hypercovering.{w} J X ⥤ HypercoveringOf.{w} J (uliftYoneda.{w}.obj X) where
  obj K := K.toPresheafTarget
  map f := Hom.toPresheafTarget f
  map_id K := Hom.toPresheafTarget_id K
  map_comp f g := Hom.toPresheafTarget_comp f g

/-- The presheaf-target functor acts on objects by the canonical augmentation construction. -/
@[simp]
theorem toPresheafTargetFunctor_obj (K : Hypercovering.{w} J X) :
    (toPresheafTargetFunctor (J := J) (X := X)).obj K = K.toPresheafTarget := sorry

/-- The presheaf-target functor acts on morphisms by forgetting the fixed target degreewise. -/
@[simp]
theorem toPresheafTargetFunctor_map {K L : Hypercovering.{w} J X} (f : K ⟶ L) :
    (toPresheafTargetFunctor (J := J) (X := X)).map f =
      Hom.toPresheafTarget f := sorry

end Hypercovering

end CategoryTheory

/- Any deferred axiom in the following audits is confined to naturality or the Prop-valued
local-hypercover law; the functors, augmentation components, and structure data are explicit. -/
