module

public import Mathlib.CategoryTheory.Limits.Final
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram

/-!
# Transport of essentially constant presentations

This file records the functoriality of presentation-wise essential constancy.  The APIs are
attached to the cone, cocone, or diagram predicate they preserve, rather than to a particular
chapter application.  In particular, they centralize transport across diagram and vertex
isomorphisms, equivalences of indexing categories, and final or initial extension.
-/

@[expose] public section

open CategoryTheory.Limits

universe uI vI uJ vJ uC vC

namespace CategoryTheory

namespace Limits.Cocone.IsEssentiallyConstant

/-- Transport an essentially constant cocone presentation across an isomorphism of diagrams. -/
theorem precomposeIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} {c : Cocone M} (hc : c.IsEssentiallyConstant) (e : M ≅ N) :
    ((Cocone.precompose e.inv).obj c).IsEssentiallyConstant := sorry

/-- Transport an essentially constant cocone presentation across an isomorphism of vertices. -/
theorem extendIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c : Cocone M} (hc : c.IsEssentiallyConstant) {X : C} (e : c.pt ≅ X) :
    (c.extend e.hom).IsEssentiallyConstant := sorry

/-- Transport an essentially constant cocone presentation across an isomorphism of cocones. -/
theorem ofIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c c' : Cocone M} (hc : c.IsEssentiallyConstant) (e : c ≅ c') :
    c'.IsEssentiallyConstant := sorry

/-- Essential constancy of cocone presentations is invariant under isomorphism of cocones. -/
theorem iff_of_iso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c c' : Cocone M} (e : c ≅ c') :
    c.IsEssentiallyConstant ↔ c'.IsEssentiallyConstant := sorry

/-- Extend an essentially constant cocone presentation along a final functor. -/
theorem extendFinal {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsFiltered I] (H : I ⥤ J) [H.Final] {M : J ⥤ C} {c : Cocone (H ⋙ M)}
    (hc : c.IsEssentiallyConstant) :
    ((Functor.Final.extendCocone).obj c).IsEssentiallyConstant := sorry

end Limits.Cocone.IsEssentiallyConstant

namespace Limits.Cone.IsEssentiallyConstant

/-- Transport an essentially constant cone presentation across an isomorphism of diagrams. -/
theorem postcomposeIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} {c : Cone M} (hc : c.IsEssentiallyConstant) (e : M ≅ N) :
    ((Cone.postcompose e.hom).obj c).IsEssentiallyConstant := sorry

/-- Transport an essentially constant cone presentation across an isomorphism of vertices. -/
theorem extendIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c : Cone M} (hc : c.IsEssentiallyConstant) {X : C} (e : c.pt ≅ X) :
    (c.extend e.inv).IsEssentiallyConstant := sorry

/-- Transport an essentially constant cone presentation across an isomorphism of cones. -/
theorem ofIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c c' : Cone M} (hc : c.IsEssentiallyConstant) (e : c ≅ c') :
    c'.IsEssentiallyConstant := sorry

/-- Essential constancy of cone presentations is invariant under isomorphism of cones. -/
theorem iff_of_iso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c c' : Cone M} (e : c ≅ c') :
    c.IsEssentiallyConstant ↔ c'.IsEssentiallyConstant := sorry

/-- Extend an essentially constant cone presentation along an initial functor. -/
theorem extendInitial {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsCofiltered I] (H : I ⥤ J) [H.Initial] {M : J ⥤ C} {c : Cone (H ⋙ M)}
    (hc : c.IsEssentiallyConstant) :
    ((Functor.Initial.extendCone).obj c).IsEssentiallyConstant := sorry

end Limits.Cone.IsEssentiallyConstant

namespace IsFiltered.IsEssentiallyConstant

/-- Transport essential constancy of a filtered-oriented diagram across an isomorphism. -/
theorem ofIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} (e : M ≅ N) (hM : IsFiltered.IsEssentiallyConstant M) :
    IsFiltered.IsEssentiallyConstant N := sorry

/-- Essential constancy of filtered-oriented diagrams is invariant under isomorphism. -/
theorem iff_of_iso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} (e : M ≅ N) :
    IsFiltered.IsEssentiallyConstant M ↔ IsFiltered.IsEssentiallyConstant N := sorry

/-- Restriction of an essentially constant filtered-oriented diagram along an equivalence remains
essentially constant. -/
theorem whiskerEquivalence {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    (e : J ≌ I) {M : I ⥤ C} (hM : IsFiltered.IsEssentiallyConstant M) :
    IsFiltered.IsEssentiallyConstant (e.functor ⋙ M) := sorry

/-- Essential constancy of a filtered-oriented diagram is invariant under reindexing by an
equivalence. -/
theorem whiskerEquivalence_iff {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    (e : J ≌ I) (M : I ⥤ C) :
    IsFiltered.IsEssentiallyConstant M ↔ IsFiltered.IsEssentiallyConstant (e.functor ⋙ M) := sorry

/-- Restricting an essentially constant diagram along a final functor from a filtered category
preserves essential constancy. -/
theorem whiskerFinal {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsFiltered I]
    (H : I ⥤ J) [H.Final] {M : J ⥤ C}
    (hM : IsFiltered.IsEssentiallyConstant M) :
    IsFiltered.IsEssentiallyConstant (H ⋙ M) := sorry

/-- Essential constancy detected after restriction along a final functor from a filtered
category holds for the original diagram. -/
theorem of_whiskerFinal {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsFiltered I]
    (H : I ⥤ J) [H.Final] {M : J ⥤ C}
    (hM : IsFiltered.IsEssentiallyConstant (H ⋙ M)) :
    IsFiltered.IsEssentiallyConstant M := sorry

/-- Essential constancy of a filtered-oriented diagram is detected by restriction along a final
functor from a filtered category. -/
@[stacks 05PV "final reindexing of essentially constant diagrams"]
theorem whiskerFinal_iff {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsFiltered I]
    (H : I ⥤ J) [H.Final] (M : J ⥤ C) :
    IsFiltered.IsEssentiallyConstant M ↔
      IsFiltered.IsEssentiallyConstant (H ⋙ M) := sorry

end IsFiltered.IsEssentiallyConstant

namespace IsCofiltered.IsEssentiallyConstant

/-- Transport essential constancy of a cofiltered-oriented diagram across an isomorphism. -/
theorem ofIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} (e : M ≅ N) (hM : IsCofiltered.IsEssentiallyConstant M) :
    IsCofiltered.IsEssentiallyConstant N := sorry

/-- Essential constancy of cofiltered-oriented diagrams is invariant under isomorphism. -/
theorem iff_of_iso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} (e : M ≅ N) :
    IsCofiltered.IsEssentiallyConstant M ↔ IsCofiltered.IsEssentiallyConstant N := sorry

/-- Restriction of an essentially constant cofiltered-oriented diagram along an equivalence
remains essentially constant. -/
theorem whiskerEquivalence {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    (e : J ≌ I) {M : I ⥤ C} (hM : IsCofiltered.IsEssentiallyConstant M) :
    IsCofiltered.IsEssentiallyConstant (e.functor ⋙ M) := sorry

/-- Essential constancy of a cofiltered-oriented diagram is invariant under reindexing by an
equivalence. -/
theorem whiskerEquivalence_iff {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    (e : J ≌ I) (M : I ⥤ C) :
    IsCofiltered.IsEssentiallyConstant M ↔
      IsCofiltered.IsEssentiallyConstant (e.functor ⋙ M) := sorry

/-- Restricting an essentially constant diagram along an initial functor from a cofiltered
category preserves essential constancy. -/
theorem whiskerInitial {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] {M : J ⥤ C}
    (hM : IsCofiltered.IsEssentiallyConstant M) :
    IsCofiltered.IsEssentiallyConstant (H ⋙ M) := sorry

/-- Essential constancy detected after restriction along an initial functor from a cofiltered
category holds for the original diagram. -/
theorem of_whiskerInitial {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] {M : J ⥤ C}
    (hM : IsCofiltered.IsEssentiallyConstant (H ⋙ M)) :
    IsCofiltered.IsEssentiallyConstant M := sorry

/-- Essential constancy of a cofiltered-oriented diagram is detected by restriction along an
initial functor from a cofiltered category. -/
@[stacks 05PV "initial reindexing of essentially constant diagrams"]
theorem whiskerInitial_iff {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] (M : J ⥤ C) :
    IsCofiltered.IsEssentiallyConstant M ↔
      IsCofiltered.IsEssentiallyConstant (H ⋙ M) := sorry

end IsCofiltered.IsEssentiallyConstant

end CategoryTheory
