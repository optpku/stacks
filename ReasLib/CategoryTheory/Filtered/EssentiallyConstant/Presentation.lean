/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.Cones

/-!
# Presentation-level essential constancy of cones and cocones

An essentially constant cocone has a split-epimorphic leg and eventual factorizations through the
chosen section.  Dually, an essentially constant cone has a split-monomorphic leg and eventual
factorizations through the chosen retraction.

These predicates are attached to a specified cone or cocone and require no filteredness assumption.
Diagram-level existence and the resulting universal properties are separate layers.
-/

@[expose] public section

open CategoryTheory

universe uI vI uC vC uD vD

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/-
The invariant notion of an ind- or pro-object isomorphic to a constant one is intentionally
separate.  The predicates here are presentation-level certificates attached to chosen cocones or
cones and impose no smallness boundary.

For the filtered orientation, the stored equality is the commutativity of

```
                         M.map jk
       M.obj j ───────────────────────────▶ M.obj k
              │                                  ▲
   c.ι.app j  │                                  │  M.map ik
              ▼                                  │
            c.pt ─────────────────────────▶ M.obj i
                         σ.section_
```

and `σ.section_ ≫ c.ι.app i = 𝟙 c.pt`.  The cofiltered orientation is the dual diagram

```
                         M.map ki
       M.obj k ───────────────────────────▶ M.obj i
              │                                  │
     M.map kj │                                  │ σ.retraction
              ▼                                  ▼
       M.obj j ◀────────────────────────────── c.pt
                         c.π.app j
```

with `c.π.app i ≫ σ.retraction = 𝟙 c.pt`.  `SplitEpi` and `SplitMono` are the canonical owners of
the distinguished splitting data.  Mathlib's `Functor.IsEventuallyConstantFrom` and
`Functor.IsEventuallyConstantTo` are strictly stronger: they require all sufficiently outgoing or
incoming transition maps to be isomorphisms.

The predicates do not take `[IsFiltered I]` or `[IsCofiltered I]`: neither their displayed data
nor the universal (co)limit construction uses those classes. Namespacing the two owners on
`Cocone` and `Cone` makes the orientation visible.
-/

namespace Cocone

/-- A cocone is essentially constant with value its vertex if one leg is split epi and every
transition from another stage eventually factors through its section. -/
@[stacks 05PU "filtered cocone: split leg and eventual factorization"]
def IsEssentiallyConstant {M : I ⥤ C} (c : Cocone M) : Prop :=
  ∃ (i : I) (σ : SplitEpi (c.ι.app i)),
    ∀ j : I, ∃ (k : I) (ik : i ⟶ k) (jk : j ⟶ k),
      M.map jk = c.ι.app j ≫ σ.section_ ≫ M.map ik

/-- The textbook section-and-factorization formulation of essential constancy for a cocone. -/
theorem isEssentiallyConstant_iff {M : I ⥤ C} (c : Cocone M) :
    c.IsEssentiallyConstant ↔
      ∃ (i : I) (s : c.pt ⟶ M.obj i),
        s ≫ c.ι.app i = 𝟙 c.pt ∧
          ∀ j : I, ∃ (k : I) (ik : i ⟶ k) (jk : j ⟶ k),
            M.map jk = c.ι.app j ≫ s ≫ M.map ik := by
  constructor
  · rintro ⟨i, σ, hσ⟩
    exact ⟨i, σ.section_, σ.id, hσ⟩
  · rintro ⟨i, s, hs, h⟩
    exact ⟨i, { section_ := s, id := hs }, h⟩

namespace IsEssentiallyConstant

variable {D : Type uD} [Category.{vD} D]

/-- The selected stage of an essentially constant cocone presentation.  This is the single
choice boundary for clients that need a distinguished index. -/
@[stacks 05PU "selected filtered stage"]
noncomputable def stage {M : I ⥤ C} {c : Cocone M}
    (hc : c.IsEssentiallyConstant) : I :=
  hc.choose

/-- The split epimorphism carried by the selected leg of an essentially constant cocone. -/
@[stacks 05PU "selected filtered split epimorphism"]
noncomputable def stageSplitEpi {M : I ⥤ C} {c : Cocone M}
    (hc : c.IsEssentiallyConstant) :
    SplitEpi (c.ι.app hc.stage) :=
  hc.choose_spec.choose

/-- The eventual factorization specification of the selected cocone stage. -/
@[stacks 05PU "filtered stage factorization"]
theorem stage_spec {M : I ⥤ C} {c : Cocone M}
    (hc : c.IsEssentiallyConstant) (j : I) :
    ∃ (k : I) (ik : hc.stage ⟶ k) (jk : j ⟶ k),
      M.map jk = c.ι.app j ≫ hc.stageSplitEpi.section_ ≫ M.map ik := by
  exact hc.choose_spec.choose_spec j

/-- Postcomposition preserves an essentially constant cocone presentation. -/
theorem map {M : I ⥤ C} {c : Cocone M} (hc : c.IsEssentiallyConstant) (F : C ⥤ D) :
    (F.mapCocone c).IsEssentiallyConstant := by
  rcases hc with ⟨i, σ, hσ⟩
  refine ⟨i, σ.map F, ?_⟩
  intro j
  obtain ⟨k, ik, jk, h⟩ := hσ j
  refine ⟨k, ik, jk, ?_⟩
  simpa only [Functor.map_comp] using! congrArg F.map h

end IsEssentiallyConstant

end Cocone

namespace Cone

/-- A cone is essentially constant with value its vertex if one leg is split mono and every
transition to another stage eventually factors through its retraction. -/
@[stacks 05PU "cofiltered cone: split leg and eventual factorization"]
def IsEssentiallyConstant {M : I ⥤ C} (c : Cone M) : Prop :=
  ∃ (i : I) (σ : SplitMono (c.π.app i)),
    ∀ j : I, ∃ (k : I) (ki : k ⟶ i) (kj : k ⟶ j),
      M.map kj = M.map ki ≫ σ.retraction ≫ c.π.app j

/-- The textbook retraction-and-factorization formulation of essential constancy for a cone. -/
theorem isEssentiallyConstant_iff {M : I ⥤ C} (c : Cone M) :
    c.IsEssentiallyConstant ↔
      ∃ (i : I) (r : M.obj i ⟶ c.pt),
        c.π.app i ≫ r = 𝟙 c.pt ∧
          ∀ j : I, ∃ (k : I) (ki : k ⟶ i) (kj : k ⟶ j),
            M.map kj = M.map ki ≫ r ≫ c.π.app j := by
  constructor
  · rintro ⟨i, σ, hσ⟩
    exact ⟨i, σ.retraction, σ.id, hσ⟩
  · rintro ⟨i, r, hr, h⟩
    exact ⟨i, { retraction := r, id := hr }, h⟩

/-- Essential constancy of a cone is the categorical dual of essential constancy of its opposite
cocone. -/
theorem isEssentiallyConstant_iff_op {M : I ⥤ C} (c : Cone M) :
    c.IsEssentiallyConstant ↔ c.op.IsEssentiallyConstant := by
  rw [isEssentiallyConstant_iff, Cocone.isEssentiallyConstant_iff]
  constructor
  · rintro ⟨i, r, hr, h⟩
    refine ⟨Opposite.op i, r.op, ?_, ?_⟩
    · simpa using! congrArg Quiver.Hom.op hr
    · intro j
      obtain ⟨k, ki, kj, hkj⟩ := h j.unop
      refine ⟨Opposite.op k, ki.op, kj.op, ?_⟩
      simpa [Category.assoc] using! congrArg Quiver.Hom.op hkj
  · rintro ⟨i, s, hs, h⟩
    refine ⟨i.unop, s.unop, ?_, ?_⟩
    · simpa using! congrArg Quiver.Hom.unop hs
    · intro j
      obtain ⟨k, ik, jk, hjk⟩ := h (Opposite.op j)
      refine ⟨k.unop, ik.unop, jk.unop, ?_⟩
      simpa [Category.assoc] using! congrArg Quiver.Hom.unop hjk

namespace IsEssentiallyConstant

variable {D : Type uD} [Category.{vD} D]

/-- The selected stage of an essentially constant cone presentation. -/
@[stacks 05PU "selected cofiltered stage"]
noncomputable def stage {M : I ⥤ C} {c : Cone M}
    (hc : c.IsEssentiallyConstant) : I :=
  hc.choose

/-- The split monomorphism carried by the selected leg of an essentially constant cone. -/
@[stacks 05PU "selected cofiltered split monomorphism"]
noncomputable def stageSplitMono {M : I ⥤ C} {c : Cone M}
    (hc : c.IsEssentiallyConstant) :
    SplitMono (c.π.app hc.stage) :=
  hc.choose_spec.choose

/-- The eventual factorization specification of the selected cone stage. -/
@[stacks 05PU "cofiltered stage factorization"]
theorem stage_spec {M : I ⥤ C} {c : Cone M}
    (hc : c.IsEssentiallyConstant) (j : I) :
    ∃ (k : I) (ki : k ⟶ hc.stage) (kj : k ⟶ j),
      M.map kj = M.map ki ≫ hc.stageSplitMono.retraction ≫ c.π.app j := by
  exact hc.choose_spec.choose_spec j

/-- Taking opposites sends an essentially constant cone to an essentially constant cocone.
This named direction avoids forcing consumers to rewrite with
`Cone.isEssentiallyConstant_iff_op` and transport across the displayed opposite cone. -/
theorem op {M : I ⥤ C} {c : Cone M} (hc : c.IsEssentiallyConstant) :
    c.op.IsEssentiallyConstant := by
  exact (Cone.isEssentiallyConstant_iff_op c).mp hc

/-- Postcomposition preserves an essentially constant cone presentation. -/
theorem map {M : I ⥤ C} {c : Cone M} (hc : c.IsEssentiallyConstant) (F : C ⥤ D) :
    (F.mapCone c).IsEssentiallyConstant := by
  rcases hc with ⟨i, σ, hσ⟩
  refine ⟨i, σ.map F, ?_⟩
  intro j
  obtain ⟨k, ki, kj, h⟩ := hσ j
  refine ⟨k, ki, kj, ?_⟩
  simpa only [Functor.map_comp] using! congrArg F.map h

end IsEssentiallyConstant

end Cone

namespace Cocone.IsEssentiallyConstant

/-- Taking opposites sends an essentially constant cocone to an essentially constant cone.
This is the dual elimination form of `Cone.IsEssentiallyConstant.op`. -/
theorem op {M : I ⥤ C} {c : Cocone M} (hc : c.IsEssentiallyConstant) :
    c.op.IsEssentiallyConstant := by
  rcases hc with ⟨i, σ, hσ⟩
  refine ⟨Opposite.op i, σ.op, ?_⟩
  intro j
  obtain ⟨k, ik, jk, h⟩ := hσ j.unop
  refine ⟨Opposite.op k, ik.op, jk.op, ?_⟩
  simpa [Category.assoc] using! congrArg Quiver.Hom.op h

end Cocone.IsEssentiallyConstant



end CategoryTheory.Limits
