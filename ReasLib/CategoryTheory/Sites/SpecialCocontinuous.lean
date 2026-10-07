module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# Special cocontinuous functors of sites

Special cocontinuity is the source-facing five-condition comparison criterion for a functor of
sites.  It is weaker than being a dense-subsite presentation, so the two notions are kept
separate and connected by a one-way bridge.
-/

@[expose] public section

open CategoryTheory

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A functor is source-locally faithful when arrows identified by the functor
become equal after restriction along a covering sieve in the source site. -/
class IsSourceLocallyFaithful (G : C ⥤ D) (J : GrothendieckTopology C) : Prop where
  /-- The equalizer sieve of two arrows identified by `G` is covering. -/
  equalizer_mem {U' U : C} (a b : U' ⟶ U) (h : G.map a = G.map b) :
    Sieve.equalizer a b ∈ J U'

/-- A functor is source-locally full when arrows between objects in its image
locally lift along a covering sieve in the source site. -/
class IsSourceLocallyFull (G : C ⥤ D) (J : GrothendieckTopology C) : Prop where
  /-- The image sieve of an arrow between image objects is covering. -/
  imageSieve_mem {U' U : C} (c : G.obj U' ⟶ G.obj U) : G.imageSieve c ∈ J U'

/-- A special cocontinuous functor is continuous and cocontinuous, is locally faithful and
locally full over the source topology, and is cover-dense in the target. These are five
independent conditions; a dense-subsite presentation is a stronger notion. -/
@[stacks 03CG]
class IsSpecialCocontinuous (G : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) : Prop where
  /-- The functor is continuous. -/
  toIsContinuous : G.IsContinuous J K
  /-- The functor is cocontinuous. -/
  toIsCocontinuous : G.IsCocontinuous J K
  /-- Arrows identified by `G` become equal after restriction along a source cover. -/
  sourceLocallyFaithful :
    ∀ {U' U : C} (a b : U' ⟶ U), G.map a = G.map b → Sieve.equalizer a b ∈ J U'
  /-- Arrows between objects in the image of `G` locally lift over the source topology. -/
  sourceLocallyFull :
    ∀ {U' U : C} (c : G.obj U' ⟶ G.obj U), G.imageSieve c ∈ J U'
  /-- Every target object is covered by objects in the image of `G`. -/
  toIsCoverDense : G.IsCoverDense K

attribute [instance] IsSpecialCocontinuous.toIsContinuous
attribute [instance] IsSpecialCocontinuous.toIsCocontinuous
attribute [instance] IsSpecialCocontinuous.toIsCoverDense

/-- Extract source-local faithfulness from special cocontinuity. This is an
explicit projection rather than a global instance because the target topology
of `IsSpecialCocontinuous` is not determined by the standalone mixin. -/
theorem IsSpecialCocontinuous.toSourceLocallyFaithful
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsSpecialCocontinuous J K] : G.IsSourceLocallyFaithful J := sorry

/-- Extract source-local fullness from special cocontinuity. This is an
explicit projection for the same target-topology inference reason as
`toSourceLocallyFaithful`. -/
theorem IsSpecialCocontinuous.toSourceLocallyFull
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsSpecialCocontinuous J K] : G.IsSourceLocallyFull J := sorry

/-- A continuous, cocontinuous, source-locally faithful, source-locally full, cover-dense
functor induces an equivalence through its cocontinuous direct image on set-valued sheaves. -/
@[stacks 03A0]
theorem directImage_isEquivalence {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (G : C ⥤ D)
    [G.IsContinuous J K] [G.IsCocontinuous J K]
    [G.IsSourceLocallyFaithful J] [G.IsSourceLocallyFull J] [G.IsCoverDense K]
    [∀ P : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension P] :
    (G.sheafPushforwardCocontinuous (Type w) J K).IsEquivalence := sorry

/-- The direct-image comparison theorem specialized to a special cocontinuous
functor. -/
theorem IsSpecialCocontinuous.directImage_isEquivalence
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} (G : C ⥤ D)
    [G.IsSpecialCocontinuous J K]
    [∀ P : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension P] :
    (G.sheafPushforwardCocontinuous (Type w) J K).IsEquivalence := sorry

namespace IsSpecialCocontinuous

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The source-local faithfulness condition of a special cocontinuous functor. -/
theorem equalizer_mem (G : C ⥤ D) [G.IsSpecialCocontinuous J K]
    {U' U : C} (a b : U' ⟶ U) (h : G.map a = G.map b) :
    Sieve.equalizer a b ∈ J U' := sorry

/-- The source-local fullness condition of a special cocontinuous functor. -/
theorem imageSieve_mem (G : C ⥤ D) [G.IsSpecialCocontinuous J K]
    {U' U : C} (c : G.obj U' ⟶ G.obj U) : G.imageSieve c ∈ J U' := sorry

end IsSpecialCocontinuous

/-- Special cocontinuity is equivalent to its five source-facing comparison conditions. -/
theorem isSpecialCocontinuous_iff
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) :
    G.IsSpecialCocontinuous J K ↔
      G.IsContinuous J K ∧ G.IsCocontinuous J K ∧
        (∀ {U' U : C} (a b : U' ⟶ U),
          G.map a = G.map b → Sieve.equalizer a b ∈ J U') ∧
        (∀ {U' U : C} (c : G.obj U' ⟶ G.obj U), G.imageSieve c ∈ J U') ∧
        G.IsCoverDense K := sorry

namespace IsDenseSubsite

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- A dense subsite is a canonical strengthening of special cocontinuity. -/
theorem isSpecialCocontinuous (G : C ⥤ D) [G.IsDenseSubsite J K] :
    G.IsSpecialCocontinuous J K := sorry

end IsDenseSubsite

attribute [instance] IsDenseSubsite.isSpecialCocontinuous

end CategoryTheory.Functor
