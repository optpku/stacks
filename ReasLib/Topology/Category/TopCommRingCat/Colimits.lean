/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Category.TopCommRingCat

/-!
# Colimits of topological commutative rings
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace TopCommRingCat

section Construction

variable {J : Type v} [Category.{w} J] {F : J ⥤ TopCommRingCat.{u}}
  (c : Cocone (F ⋙ forget₂ TopCommRingCat CommRingCat))

/-- The finest ring topology on an algebraic cocone point for which all its legs are
continuous. Taking the infimum in `RingTopology` ensures that the ring operations remain
continuous; the final topology of the underlying spaces need not have this property. -/
def coconeRingTopology : RingTopology c.pt :=
  sInf {t : RingTopology c.pt | ∀ j,
    Continuous[(F.obj j).isTopologicalSpace, t.toTopologicalSpace] (c.ι.app j)}

theorem continuous_coconeRingTopology (j : J) :
    Continuous[(F.obj j).isTopologicalSpace, (coconeRingTopology c).toTopologicalSpace]
      (c.ι.app j) :=
  continuous_sInf_rng.2 <| Set.forall_mem_image.2 fun _ ht => ht j

/-- Lift an algebraic cocone by giving its point the finest compatible ring topology. -/
def coconeOfCoconeForget : Cocone F :=
  letI := (coconeRingTopology c).toTopologicalSpace
  letI := (coconeRingTopology c).toIsTopologicalRing
  { pt := of c.pt
    ι :=
      { app j := ⟨(c.ι.app j).hom, continuous_coconeRingTopology c j⟩
        naturality i j f := by
          ext x
          exact ConcreteCategory.congr_hom (c.ι.naturality f) x } }

/-- A ring homomorphism from the lifted cocone point is continuous whenever its composites
with all the cocone legs are continuous. -/
theorem continuous_from_coconeRingTopology {S : Type*} [Ring S]
    [TopologicalSpace S] [IsTopologicalRing S] (f : c.pt →+* S)
    (hf : ∀ j, Continuous[(F.obj j).isTopologicalSpace, inferInstance]
      (f ∘ c.ι.app j)) :
    Continuous[(coconeRingTopology c).toTopologicalSpace, inferInstance] f := by
  let t : RingTopology c.pt :=
    { toTopologicalSpace := TopologicalSpace.induced f inferInstance
      toContinuousAdd := continuousAdd_induced f
      toContinuousMul := continuousMul_induced f
      toContinuousNeg := ContinuousNeg.induced f }
  apply continuous_iff_le_induced.2
  change (sInf (RingTopology.toTopologicalSpace ''
    {t : RingTopology c.pt | ∀ j,
      Continuous[(F.obj j).isTopologicalSpace, t.toTopologicalSpace] (c.ι.app j)})) ≤ _
  exact sInf_le ⟨t, fun j => continuous_induced_rng.2 (hf j), rfl⟩

/-- An algebraic colimit cocone becomes a colimit of topological commutative rings with
the finest compatible ring topology. Its descending maps are the algebraic descending maps. -/
noncomputable def isColimitCoconeOfForget (hc : IsColimit c) :
    IsColimit (coconeOfCoconeForget c) := by
  refine IsColimit.ofFaithful (forget₂ TopCommRingCat CommRingCat) (ht := hc)
    (fun s => ⟨(hc.desc ((forget₂ TopCommRingCat CommRingCat).mapCocone s)).hom, ?_⟩)
    (fun _ => rfl)
  apply continuous_from_coconeRingTopology c
  intro j
  refine Continuous.congr (s.ι.app j).2 (fun x => ?_)
  exact (ConcreteCategory.congr_hom
    (hc.fac ((forget₂ TopCommRingCat CommRingCat).mapCocone s) j) x).symm

end Construction

/-- The category of topological commutative rings has all small colimits. -/
@[stacks 0B24 "topological commutative rings have colimits"]
instance hasColimits : HasColimits TopCommRingCat.{u} where
  has_colimits_of_shape _ _ :=
    { has_colimit F := HasColimit.mk
        { cocone := coconeOfCoconeForget
            (CommRingCat.Colimits.colimitCocone (F ⋙ forget₂ TopCommRingCat CommRingCat))
          isColimit := isColimitCoconeOfForget _
            (CommRingCat.Colimits.colimitIsColimit
              (F ⋙ forget₂ TopCommRingCat CommRingCat)) } }

/-- Forgetting a topological commutative ring to its commutative ring preserves all small
colimits. -/
@[stacks 0B24 "colimits are preserved by the forgetful functor to commutative rings"]
instance forgetToCommRingCat_preservesColimits :
    PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) where
  preservesColimitsOfShape {_} _ :=
    { preservesColimit {F} :=
        preservesColimit_of_preserves_colimit_cocone
          (isColimitCoconeOfForget _
            (CommRingCat.Colimits.colimitIsColimit
              (F ⋙ forget₂ TopCommRingCat CommRingCat)))
          (CommRingCat.Colimits.colimitIsColimit
            (F ⋙ forget₂ TopCommRingCat CommRingCat)) }

end TopCommRingCat
