module

public import ReasLib.CategoryTheory.Sites.IndexedSite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

@[expose] public section

universe w uC uD vC vD

namespace CategoryTheory.PreZeroHypercover

open Category Limits

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- A functor between selected indexed-family sites is continuous if it sends every selected
covering family to a selected covering family and preserves pullbacks along its members. -/
class IsContinuous (u : C ⥤ D)
    (J : ∀ target : C, Set (PreZeroHypercover.{w} target))
    (K : ∀ target : D, Set (PreZeroHypercover.{w} target))
    [IsSite J] [IsSite K] : Prop where
  /-- The indexed image of every selected covering family is selected. -/
  map_mem : ∀ {target : C} (family : PreZeroHypercover.{w} target),
    family ∈ J target → family.map u ∈ K (u.obj target)
  /-- Pullbacks along each member of a selected covering family are preserved. -/
  preservesPullback : ∀ {target : C} (family : PreZeroHypercover.{w} target),
    family ∈ J target → ∀ (index : family.I₀) {T : C} (base : T ⟶ target),
      PreservesLimit (cospan base (family.f index)) u

namespace IsContinuous

variable {u : C ⥤ D}
variable {J : ∀ target : C, Set (PreZeroHypercover.{w} target)}
variable {K : ∀ target : D, Set (PreZeroHypercover.{w} target)}
variable [IsSite J] [IsSite K]

/-- Indexed-family continuity is equivalent to preservation of selected image families and
pullbacks along their members. -/
theorem iff : IsContinuous u J K ↔
    (∀ {target : C} (family : PreZeroHypercover.{w} target),
      family ∈ J target → family.map u ∈ K (u.obj target)) ∧
    (∀ {target : C} (family : PreZeroHypercover.{w} target),
      family ∈ J target → ∀ (index : family.I₀) {T : C} (base : T ⟶ target),
        PreservesLimit (cospan base (family.f index)) u) := sorry

/-- The canonical comparison on a pullback along a selected covering member is an
isomorphism for a continuous functor. -/
theorem pullbackComparison_isIso (h : IsContinuous u J K)
    {target : C} (family : PreZeroHypercover.{w} target) (hfamily : family ∈ J target)
    (index : family.I₀) {T : C} (base : T ⟶ target)
    [HasPullback base (family.f index)]
    [HasPullback (u.map base) (u.map (family.f index))] :
    IsIso (pullbackComparison u base (family.f index)) := sorry

/-- The identity functor is continuous for every selected indexed-family site. -/
instance id (J : ∀ target : C, Set (PreZeroHypercover.{w} target)) [IsSite J] :
    IsContinuous (𝟭 C) J J := sorry

end IsContinuous

end CategoryTheory.PreZeroHypercover
