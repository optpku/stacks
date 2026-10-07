module

public import ReasLib.CategoryTheory.Filtered.ModuloKernel

/-!
# Transport for filtered functors modulo their kernel

Filteredness modulo a functor's kernel depends only on the isomorphism class of the diagram and
is invariant under equivalence of indexing categories. These statements keep downstream code at
the quotient-independent predicate layer.
-/

@[expose] public section

universe vI uI vJ uJ vC uC

namespace CategoryTheory.Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

namespace IsFilteredModuloKernel

/-- Transport filteredness modulo the kernel across an isomorphism of diagrams. -/
theorem ofIso {M N : I ⥤ C} (e : M ≅ N) (hM : M.IsFilteredModuloKernel) :
    N.IsFilteredModuloKernel := sorry

/-- Filteredness modulo the kernel is invariant under isomorphism of diagrams. -/
theorem iff_of_iso {M N : I ⥤ C} (e : M ≅ N) :
    M.IsFilteredModuloKernel ↔ N.IsFilteredModuloKernel := sorry

/-- Restriction along an equivalence of indexing categories preserves filteredness modulo the
kernel. -/
theorem whiskerEquivalence (e : J ≌ I) {M : I ⥤ C}
    (hM : M.IsFilteredModuloKernel) :
    (e.functor ⋙ M).IsFilteredModuloKernel := sorry

/-- Filteredness modulo the kernel is invariant under reindexing by an equivalence. -/
theorem whiskerEquivalence_iff (e : J ≌ I) (M : I ⥤ C) :
    M.IsFilteredModuloKernel ↔ (e.functor ⋙ M).IsFilteredModuloKernel := sorry

end IsFilteredModuloKernel

namespace IsCofilteredModuloKernel

/-- Transport cofilteredness modulo the kernel across an isomorphism of diagrams. -/
theorem ofIso {M N : I ⥤ C} (e : M ≅ N) (hM : M.IsCofilteredModuloKernel) :
    N.IsCofilteredModuloKernel := sorry

/-- Cofilteredness modulo the kernel is invariant under isomorphism of diagrams. -/
theorem iff_of_iso {M N : I ⥤ C} (e : M ≅ N) :
    M.IsCofilteredModuloKernel ↔ N.IsCofilteredModuloKernel := sorry

/-- Restriction along an equivalence of indexing categories preserves cofilteredness modulo the
kernel. -/
theorem whiskerEquivalence (e : J ≌ I) {M : I ⥤ C}
    (hM : M.IsCofilteredModuloKernel) :
    (e.functor ⋙ M).IsCofilteredModuloKernel := sorry

/-- Cofilteredness modulo the kernel is invariant under reindexing by an equivalence. -/
theorem whiskerEquivalence_iff (e : J ≌ I) (M : I ⥤ C) :
    M.IsCofilteredModuloKernel ↔ (e.functor ⋙ M).IsCofilteredModuloKernel := sorry

end IsCofilteredModuloKernel

end CategoryTheory.Functor
