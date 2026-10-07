module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Augmentation
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Comparison
public import ReasLib.CategoryTheory.Sites.Family.Overlap.Basic

/-!
# Overlap coforks of fixed-target families

This leaf connects the site-facing `SemiRepresentableFamily.Over` model with the canonical
formal-coproduct presheaf presentation.  It names the pairwise-overlap family, its two projection
maps, and the resulting augmented cofork, independently of any topology.
-/

@[expose] public section

noncomputable section

universe w v u v' u'

namespace CategoryTheory

open Limits Opposite

namespace SemiRepresentableFamily.Over

variable {D : Type u} [Category.{v} D] {V : D}

/-- The coproduct of representable presheaves associated to a fixed-target family. -/
noncomputable abbrev toPresheaf (𝒰 : Over.{w} V) :
    Dᵒᵖ ⥤ Type (max w v) :=
  FormalCoproduct.toPresheaf.obj
    ((FormalCoproduct.forgetOver V).obj (Over.toOverFamily.obj 𝒰))

/-- The map of coproduct presheaves induced by a fixed-target-family morphism. -/
noncomputable abbrev toPresheafMap {𝒰 𝒱 : Over.{w} V} (φ : 𝒰 ⟶ 𝒱) :
    toPresheaf 𝒰 ⟶ toPresheaf 𝒱 :=
  FormalCoproduct.toPresheaf.map
    ((FormalCoproduct.forgetOver V).map (Over.toOverFamily.map φ))

/-- The canonical augmentation from the family presheaf to the representable presheaf of its
fixed target. -/
noncomputable abbrev augmentation (𝒰 : Over.{w} V) :
    toPresheaf 𝒰 ⟶ uliftYoneda.{w}.obj V :=
  FormalCoproduct.augmentation (Over.toOverFamily.obj 𝒰)

/-- The canonical augmentation is natural under a morphism of fixed-target families. -/
theorem augmentation_naturality {𝒰 𝒱 : Over.{w} V} (φ : 𝒰 ⟶ 𝒱) :
    toPresheafMap φ ≫ augmentation 𝒱 = augmentation 𝒰 := sorry

/-- The family of pairwise overlaps of the members of `𝒰`, indexed by ordered pairs. -/
noncomputable def overlapFamily (𝒰 : Over.{w} V)
    [𝒰.toPresieve.HasPairwisePullbacks] : Over.{w} V :=
  ofArrows
    (fun ij : 𝒰.index × 𝒰.index ↦ 𝒰.Overlap ij.1 ij.2)
    (fun ij ↦ 𝒰.overlapMap ij.1 ij.2)

/-- The first overlap projection lies over the common target. -/
theorem overlapFst_hom (𝒰 : Over.{w} V) [𝒰.toPresieve.HasPairwisePullbacks]
    (i j : 𝒰.index) :
    𝒰.fst i j ≫ (𝒰.obj i).hom =
      ((overlapFamily 𝒰).obj (i, j)).hom := sorry

/-- The second overlap projection lies over the common target. -/
theorem overlapSnd_hom (𝒰 : Over.{w} V) [𝒰.toPresieve.HasPairwisePullbacks]
    (i j : 𝒰.index) :
    𝒰.snd i j ≫ (𝒰.obj j).hom =
      ((overlapFamily 𝒰).obj (i, j)).hom := sorry

/-- The first projection from the pairwise-overlap family to the original family. -/
noncomputable def overlapFst (𝒰 : Over.{w} V)
    [𝒰.toPresieve.HasPairwisePullbacks] : overlapFamily 𝒰 ⟶ 𝒰 where
  α := fun ij ↦ ij.1
  f := fun ij ↦ CategoryTheory.Over.homMk
    (𝒰.fst ij.1 ij.2)
    (overlapFst_hom 𝒰 ij.1 ij.2)

/-- The second projection from the pairwise-overlap family to the original family. -/
noncomputable def overlapSnd (𝒰 : Over.{w} V)
    [𝒰.toPresieve.HasPairwisePullbacks] : overlapFamily 𝒰 ⟶ 𝒰 where
  α := fun ij ↦ ij.2
  f := fun ij ↦ CategoryTheory.Over.homMk
    (𝒰.snd ij.1 ij.2)
    (overlapSnd_hom 𝒰 ij.1 ij.2)

/-- The two overlap maps agree after the canonical augmentation to the fixed target. -/
theorem overlap_augmentation_parallel (𝒰 : Over.{w} V)
    [𝒰.toPresieve.HasPairwisePullbacks] :
    toPresheafMap (overlapFst 𝒰) ≫ augmentation 𝒰 =
      toPresheafMap (overlapSnd 𝒰) ≫ augmentation 𝒰 := sorry

/-- The canonical cofork from pairwise overlap representables to the representable presheaf of
the fixed target. -/
noncomputable def overlapCofork (𝒰 : Over.{w} V)
    [𝒰.toPresieve.HasPairwisePullbacks] :
    Cofork (toPresheafMap (overlapFst 𝒰)) (toPresheafMap (overlapSnd 𝒰)) :=
  Cofork.ofπ (augmentation 𝒰) (overlap_augmentation_parallel 𝒰)

variable {C : Type u'} [Category.{v'} C]

/-- Whiskering the overlap maps along a functor preserves their common augmentation. -/
theorem whiskerLeft_overlap_augmentation_parallel (u : C ⥤ D) (𝒰 : Over.{w} V)
    [𝒰.toPresieve.HasPairwisePullbacks] :
    u.op.whiskerLeft (toPresheafMap (overlapFst 𝒰)) ≫
        u.op.whiskerLeft (augmentation 𝒰) =
      u.op.whiskerLeft (toPresheafMap (overlapSnd 𝒰)) ≫
        u.op.whiskerLeft (augmentation 𝒰) := sorry

/-- Lemma 7.20.2 (00XK), in fixed-target-family form: restricting the overlap presentation along
`u` gives the canonical cofork from pairwise-overlap representables to the representable
presheaf of the fixed target. -/
@[stacks 00XK]
noncomputable def whiskerLeftOverlapCofork (u : C ⥤ D) (𝒰 : Over.{w} V)
    [𝒰.toPresieve.HasPairwisePullbacks] :
    Cofork
      (u.op.whiskerLeft (toPresheafMap (overlapFst 𝒰)))
      (u.op.whiskerLeft (toPresheafMap (overlapSnd 𝒰))) :=
  Cofork.ofπ
    (u.op.whiskerLeft (augmentation 𝒰))
    (whiskerLeft_overlap_augmentation_parallel u 𝒰)

end SemiRepresentableFamily.Over

end CategoryTheory
