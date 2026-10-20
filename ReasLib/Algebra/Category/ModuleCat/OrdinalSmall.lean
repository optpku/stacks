module

public import ReasLib.Algebra.Category.ModuleCat.Factorization
public import ReasLib.Algebra.Category.ModuleCat.FilteredColimit.Mono
public import ReasLib.CategoryTheory.Limits.Colimit.Representable
public import ReasLib.CategoryTheory.MorphismProperty.OrdinalSmall
public import ReasLib.SetTheory.Ordinal.Cofinality
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinal-small modules

This leaf specializes ordinal smallness to monomorphism diagrams in `ModuleCat`.  The source is a
bundled module, and its submodule lattice supplies the cardinal bound controlling stabilization
of the inverse-image submodules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace ModuleCat.OrdinalSmall

variable {R : Type u} [Ring R]

/-- The inverse image in `M` of the range of the `j`th coprojection into the colimit. -/
noncomputable def stagePreimage {α : Ordinal.{max u v}}
    (B : α.ToType ⥤ ModuleCat.{max u v} R)
    {M : ModuleCat.{max u v} R} (f : M ⟶ colimit B) (j : α.ToType) :
    Submodule R M :=
  Factorization.preimage (colimit.ι B j) f

/-- An element belongs to a stage preimage exactly when its image has a representative at that
stage. -/
@[simp]
theorem mem_stagePreimage_iff {α : Ordinal.{max u v}}
    (B : α.ToType ⥤ ModuleCat.{max u v} R)
    {M : ModuleCat.{max u v} R} (f : M ⟶ colimit B) (j : α.ToType) (x : M) :
    x ∈ stagePreimage B f j ↔ f.hom x ∈ LinearMap.range (colimit.ι B j).hom := sorry

/-- The stage preimages form a monotone family of submodules. -/
theorem stagePreimage_monotone {α : Ordinal.{max u v}}
    (B : α.ToType ⥤ ModuleCat.{max u v} R) {M : ModuleCat.{max u v} R}
    (f : M ⟶ colimit B) :
    Monotone (stagePreimage B f) := sorry

/-- Every element of the source belongs to some stage preimage for a nonempty ordinal diagram. -/
theorem mem_some_stagePreimage {α : Ordinal.{max u v}} [Nonempty α.ToType]
    (B : α.ToType ⥤ ModuleCat.{max u v} R) {M : ModuleCat.{max u v} R}
    (f : M ⟶ colimit B) (x : M) :
    ∃ j : α.ToType, x ∈ stagePreimage B f j := sorry

/-- If `M` has fewer submodules than `α.cof`, one stage preimage of every map to an
`α`-colimit is already all of `M`. -/
theorem exists_stagePreimage_eq_top
    {α : Ordinal.{max u v}} (B : α.ToType ⥤ ModuleCat.{max u v} R)
    {M : ModuleCat.{max u v} R}
    (f : M ⟶ colimit B) (hM : Cardinal.mk (Submodule R M) < α.cof) :
    ∃ j : α.ToType, stagePreimage B f j = ⊤ := sorry

/-- The Hom-colimit comparison for a nonempty ordinal diagram of monomorphisms of modules is
injective. -/
theorem injective {α : Ordinal.{max u v}} [Nonempty α.ToType]
    (M : ModuleCat.{max u v} R) (B : α.ToType ⥤ ModuleCat.{max u v} R)
    (hB : (MorphismProperty.monomorphisms (ModuleCat.{max u v} R)).IsOrdinalDiagram B) :
    Function.Injective (colimit.post B (coyoneda.obj (op M))) := sorry

/-- If the submodule lattice of `M` is smaller than `α.cof`, the Hom-colimit comparison for
every mono `α`-diagram is surjective. -/
theorem surjective
    {α : Ordinal.{max u v}} (M : ModuleCat.{max u v} R)
    (hM : Cardinal.mk (Submodule R M) < α.cof)
    (B : α.ToType ⥤ ModuleCat.{max u v} R)
    (hB : (MorphismProperty.monomorphisms (ModuleCat.{max u v} R)).IsOrdinalDiagram B) :
    Function.Surjective (colimit.post B (coyoneda.obj (op M))) := sorry

/-- If the submodule lattice of `M` is smaller than `α.cof`, the Hom-colimit comparison for
every mono `α`-diagram is bijective. -/
@[stacks 05NT "Hom-colimit comparison"]
theorem bijective
    {α : Ordinal.{max u v}} (M : ModuleCat.{max u v} R)
    (hM : Cardinal.mk (Submodule R M) < α.cof)
    (B : α.ToType ⥤ ModuleCat.{max u v} R)
    (hB : (MorphismProperty.monomorphisms (ModuleCat.{max u v} R)).IsOrdinalDiagram B) :
    Function.Bijective (colimit.post B (coyoneda.obj (op M))) := sorry

/-- `HasCardinalLT` form of ordinal smallness of a module relative to monomorphisms. -/
theorem monomorphisms_of_hasCardinalLT_cof (M : ModuleCat.{max u v} R)
    (α : Ordinal.{max u v})
    (hM : HasCardinalLT (Submodule R M) α.cof) :
    (MorphismProperty.monomorphisms (ModuleCat.{max u v} R)).IsOrdinalSmall M α := sorry

/-- A module is ordinal-small relative to monomorphisms whenever its submodule lattice is smaller
than the cofinality of the indexing ordinal. In `ModuleCat`,
monomorphisms are precisely injective linear maps. -/
@[stacks 05NT]
theorem monomorphisms_of_submodule_lt_cof (M : ModuleCat.{max u v} R)
    (α : Ordinal.{max u v})
    (hM : Cardinal.mk (Submodule R M) < α.cof) :
    (MorphismProperty.monomorphisms (ModuleCat.{max u v} R)).IsOrdinalSmall M α := sorry

end ModuleCat.OrdinalSmall
