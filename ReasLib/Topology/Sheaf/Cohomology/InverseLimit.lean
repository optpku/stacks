module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.Topology.Sheaves.InverseLimit.System
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of inverse limits of spectral spaces

This leaf owns the stagewise cohomology diagram for a compatible inverse system of abelian
sheaves. Its transition maps are built directly from pullback on cohomology, restriction to the
smaller projection open, and the pullback-form transition of the sheaf system. No direct-image
cohomology isomorphism is used.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Sheaf

noncomputable section

universe u v

namespace TopCat.Sheaf.InverseLimit.Cohomology

open TopCat.Sheaf.InverseLimit.SheafSystem

variable {I : Type u} [Category.{v} I]
variable {F : I ⥤ TopCat.{max u v}}

/-- The cohomology transition associated to `f : A ⟶ B` in `(Over i)ᵒᵖ`. It first
pulls cohomology from the stage of `A` to the stage of `B`, restricts to the projection open of
`B`, and then applies the pullback-form transition of the sheaf system. -/
@[stacks 0A37 "stage cohomology transition"]
noncomputable def transition
    (system : SheafSystem (C := AddCommGrpCat.{max u v}) F)
    (i : I) (U : Opens (F.obj i)) (p : ℕ)
    {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    (system.stageSheaf A.unop.left).H' p (projectionOpen i U A.unop) ⟶
      (system.stageSheaf B.unop.left).H' p (projectionOpen i U B.unop) :=
  pullbackCohomologyMap (F.map f.unop.left) (system.stageSheaf A.unop.left) p
      (projectionOpen i U A.unop) ≫
    ((((TopCat.Sheaf.pullback AddCommGrpCat.{max u v} (F.map f.unop.left)).obj
      (system.stageSheaf A.unop.left)).cohomologyPresheaf p).map
        (homOfLE (projectionOpen_le (F := F) i U f.unop)).op) ≫
    cohomologyMap (system.stagePullbackMap f.unop.left) p
      (projectionOpen i U B.unop)

/-- The stage cohomology transition is the canonical pullback-restriction-coefficient-map
composite. -/
theorem transition_def
    (system : SheafSystem (C := AddCommGrpCat.{max u v}) F)
    (i : I) (U : Opens (F.obj i)) (p : ℕ)
    {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    transition system i U p f =
      pullbackCohomologyMap (F.map f.unop.left) (system.stageSheaf A.unop.left) p
          (projectionOpen i U A.unop) ≫
        ((((TopCat.Sheaf.pullback AddCommGrpCat.{max u v} (F.map f.unop.left)).obj
          (system.stageSheaf A.unop.left)).cohomologyPresheaf p).map
            (homOfLE (projectionOpen_le (F := F) i U f.unop)).op) ≫
        cohomologyMap (system.stagePullbackMap f.unop.left) p
          (projectionOpen i U B.unop) := sorry

/-- The stage cohomology transition attached to an identity arrow is the identity. -/
theorem transition_id
    (system : SheafSystem (C := AddCommGrpCat.{max u v}) F)
    (i : I) (U : Opens (F.obj i)) (p : ℕ) (A : (Over i)ᵒᵖ) :
    transition system i U p (𝟙 A) = 𝟙 _ := sorry

/-- Stage cohomology transitions respect composition. -/
theorem transition_comp
    (system : SheafSystem (C := AddCommGrpCat.{max u v}) F)
    (i : I) (U : Opens (F.obj i)) (p : ℕ)
    {A B D : (Over i)ᵒᵖ} (f : A ⟶ B) (g : B ⟶ D) :
    transition system i U p (f ≫ g) =
      transition system i U p f ≫ transition system i U p g := sorry

/-- The diagram `a : j ⟶ i ↦ H^p(fₐ⁻¹(U), F_j)` with its canonical
pullback-form transitions. -/
@[stacks 0A37 "stage cohomology diagram"]
noncomputable def diagram
    (system : SheafSystem (C := AddCommGrpCat.{max u v}) F)
    (i : I) (U : Opens (F.obj i)) (p : ℕ) :
    (Over i)ᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj A := (system.stageSheaf A.unop.left).H' p (projectionOpen i U A.unop)
  map f := transition system i U p f
  map_id A := transition_id system i U p A
  map_comp f g := transition_comp system i U p f g

/-- The value of the stage cohomology diagram at `a : j ⟶ i`. -/
@[simp]
theorem diagram_obj
    (system : SheafSystem (C := AddCommGrpCat.{max u v}) F)
    (i : I) (U : Opens (F.obj i)) (p : ℕ) (A : (Over i)ᵒᵖ) :
    (diagram system i U p).obj A =
      (system.stageSheaf A.unop.left).H' p (projectionOpen i U A.unop) := sorry

/-- The morphism of the stage cohomology diagram is `transition`. -/
@[simp]
theorem diagram_map
    (system : SheafSystem (C := AddCommGrpCat.{max u v}) F)
    (i : I) (U : Opens (F.obj i)) (p : ℕ)
    {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    (diagram system i U p).map f = transition system i U p f := sorry

section Limit

variable [HasLimit F]
variable (system : SheafSystem (C := AddCommGrpCat.{max u v}) F)
variable [HasColimit system.limitPullbackDiagram]

/-- The canonical map from one stage cohomology group to cohomology of the canonical colimit
sheaf on the corresponding inverse-image open of the limit space. -/
@[stacks 0A37 "stage-to-limit cohomology map"]
noncomputable def stageMap
    (i : I) (U : Opens (F.obj i)) (p : ℕ) (A : (Over i)ᵒᵖ) :
    (diagram system i U p).obj A ⟶
      system.colimitSheaf.H' p (limitProjectionOpen i U) :=
  pullbackCohomologyMap (limit.π F A.unop.left)
      (system.stageSheaf A.unop.left) p (projectionOpen i U A.unop) ≫
    ((((TopCat.Sheaf.pullback AddCommGrpCat.{max u v} (limit.π F A.unop.left)).obj
      (system.stageSheaf A.unop.left)).cohomologyPresheaf p).map
        (homOfLE (limitProjectionOpen_le (F := F) i U A.unop)).op) ≫
    cohomologyMap
      (colimit.ι system.limitPullbackDiagram (op A.unop.left)) p
      (limitProjectionOpen i U)

/-- The maps from stage cohomology to limit cohomology commute with stage transitions. -/
theorem stageMap_naturality
    (i : I) (U : Opens (F.obj i)) (p : ℕ)
    {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    (diagram system i U p).map f ≫ stageMap system i U p B =
      stageMap system i U p A := sorry

/-- The stage maps satisfy naturality in the form required by the constant-target cocone. -/
theorem stageMap_naturality_const
    (i : I) (U : Opens (F.obj i)) (p : ℕ)
    {A B : (Over i)ᵒᵖ} (f : A ⟶ B) :
    (diagram system i U p).map f ≫ stageMap system i U p B =
      stageMap system i U p A ≫
        ((Functor.const (Over i)ᵒᵖ).obj
          (system.colimitSheaf.H' p (limitProjectionOpen i U))).map f := sorry

/-- The canonical cocone from stagewise cohomology to cohomology of the colimit sheaf on the
inverse-limit space. -/
@[stacks 0A37 "stage cohomology cocone"]
noncomputable def cocone
    (i : I) (U : Opens (F.obj i)) (p : ℕ) :
    Cocone (diagram system i U p) where
  pt := system.colimitSheaf.H' p (limitProjectionOpen i U)
  ι :=
    { app := fun A ↦ stageMap system i U p A
      naturality := fun {_ _} f ↦ stageMap_naturality_const system i U p f }

/-- The leg of the stage cohomology cocone at `a : j ⟶ i` is `stageMap`. -/
@[simp]
theorem cocone_ι_app
    (i : I) (U : Opens (F.obj i)) (p : ℕ) (A : (Over i)ᵒᵖ) :
    (cocone system i U p).ι.app A = stageMap system i U p A := sorry

/-- The canonical comparison from the colimit of stagewise cohomology to cohomology of the
canonical colimit sheaf on the inverse-image open of the limit space. -/
@[stacks 0A37 "inverse-limit cohomology comparison"]
noncomputable def comparison
    (i : I) (U : Opens (F.obj i)) (p : ℕ) :
    colimit (diagram system i U p) ⟶
      system.colimitSheaf.H' p (limitProjectionOpen i U) :=
  colimit.desc (diagram system i U p) (cocone system i U p)

/-- The inverse-limit cohomology comparison restricts at every stage to the canonical
stage-to-limit map. -/
@[reassoc, stacks 0A37 "inverse-limit cohomology comparison at a stage"]
theorem ι_comp_comparison
    (i : I) (U : Opens (F.obj i)) (p : ℕ) (A : (Over i)ᵒᵖ) :
    colimit.ι (diagram system i U p) A ≫ comparison system i U p =
      stageMap system i U p A := sorry

/-- Lemma 20.19.3 (0A37): for a cofiltered inverse system of spectral spaces with spectral
transition maps, the canonical comparison from stagewise cohomology over a compact open to
cohomology on its inverse image in the limit is an isomorphism in every degree. -/
@[stacks 0A37]
theorem comparison_isIso
    [IsCofiltered I] [∀ j : I, SpectralSpace (F.obj j)]
    (hF : ∀ {j i : I} (a : j ⟶ i), IsSpectralMap (F.map a))
    (i : I) (U : CompactOpens (F.obj i)) (p : ℕ) :
    IsIso (comparison system i U.toOpens p) := sorry

end Limit

end TopCat.Sheaf.InverseLimit.Cohomology
