/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Topology
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Absolute
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ringed sites attached to a comparison of topologies

For two topologies `τ' ≤ τ` on the same category and a ring sheaf `O'` for `τ'`, this file owns
the canonical morphism from the `τ`-ringed site with structure sheaf pulled back from `O'` to the
original `τ'`-ringed site.  Derived and module-valued consequences belong in downstream leaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace RingedSite.TopologyComparison

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

/-- The target ringed site of the comparison `τ' ≤ τ`. -/
@[stacks 0F18 "target ringed site", stacks 0F19 "target ringed site"]
noncomputable def target (O' : Sheaf τ' RingCat.{w}) : RingedSite.{u, v, w} :=
  RingedSite.ofRingSheaf τ' O'

/-- The source ringed site of the comparison `τ' ≤ τ`, with structure sheaf obtained by
inverse image from the target. -/
@[stacks 0F18 "source ringed site", stacks 0F19 "source ringed site"]
noncomputable def source
    (hle : τ' ≤ τ)
    [HasWeakSheafify τ RingCat.{w}]
    [∀ F : Cᵒᵖ ⥤ RingCat.{w}, (𝟭 C).op.HasLeftKanExtension F]
    (O' : Sheaf τ' RingCat.{w}) : RingedSite.{u, v, w} :=
  RingedSite.ofRingSheaf τ
    ((GrothendieckTopology.TopologyComparison.pullback RingCat.{w} hle).obj O')

/-- The concrete structure-sheaf map used by the topology-comparison morphism.  Keeping this map
separate from the bundled morphism gives downstream code a stable data owner. -/
@[stacks 0F18 "topology-comparison structure-sheaf map",
  stacks 0F19 "topology-comparison structure-sheaf map"]
noncomputable def structureSheafMap
    (hle : τ' ≤ τ)
    [HasWeakSheafify τ RingCat.{w}]
    [∀ F : Cᵒᵖ ⥤ RingCat.{w}, (𝟭 C).op.HasLeftKanExtension F]
    (O' : Sheaf τ' RingCat.{w}) :
    O' ⟶
      (GrothendieckTopology.TopologyComparison.pushforward RingCat.{w} hle).obj
        ((GrothendieckTopology.TopologyComparison.pullback RingCat.{w} hle).obj O') :=
  (GrothendieckTopology.TopologyComparison.adjunction RingCat.{w} hle).unit.app O'

/-- The canonical morphism of ringed sites induced by `τ' ≤ τ`. -/
@[stacks 0F18 "ringed-site topology comparison", stacks 0F19 "ringed-site topology comparison"]
noncomputable def hom
    (hle : τ' ≤ τ)
    [HasWeakSheafify τ RingCat.{w}]
    [∀ F : Cᵒᵖ ⥤ RingCat.{w}, (𝟭 C).op.HasLeftKanExtension F]
    (O' : Sheaf τ' RingCat.{w}) :
    RingedSite.Hom (source hle O') (target O') :=
  { base := 𝟭 C
    isMorphismOfSites := CategoryTheory.IsMorphismOfSites.id_of_le hle
    structureSheafMap := structureSheafMap hle O' }

/-- The base functor of the canonical topology-comparison morphism is the identity. -/
@[stacks 0F18 "topology-comparison identity base",
  stacks 0F19 "topology-comparison identity base"]
theorem hom_base
    (hle : τ' ≤ τ)
    [HasWeakSheafify τ RingCat.{w}]
    [∀ F : Cᵒᵖ ⥤ RingCat.{w}, (𝟭 C).op.HasLeftKanExtension F]
    (O' : Sheaf τ' RingCat.{w}) :
    (hom hle O').base = 𝟭 C := sorry

-- Any `sorryAx` reported for `hom` is inherited only through the Prop-valued
-- morphism-of-sites witness; its base functor and structure-sheaf map are explicit.

end RingedSite.TopologyComparison

end
