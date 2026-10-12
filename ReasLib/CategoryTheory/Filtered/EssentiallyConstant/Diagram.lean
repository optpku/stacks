/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Presentation
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Essentially constant filtered and cofiltered diagrams

A diagram is presentation-wise essentially constant when it admits an essentially constant cocone,
or dually an essentially constant cone.  The definition itself does not require the corresponding
filteredness class; that hypothesis belongs to the intended textbook applications, while the
presentation alone already determines the canonical (co)limit.
-/

@[expose] public section

open CategoryTheory.Limits

universe uI vI uC vC uD vD

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/-
The invariant notion that an associated ind- or pro-object is isomorphic to a constant one is kept
separate.  The definitions here ask only for a cocone or cone with a presentation-level
certificate and have no smallness assumption.

Mathlib already separates the two orientations as `IsFiltered.IsEventuallyConstant` and
`IsCofiltered.IsEventuallyConstant`.  We follow those namespaces, but not those predicates: they
require transition maps eventually to be isomorphisms and are strictly stronger than the Stacks
condition.  The local owners therefore say directly

    `∃ c : Cocone M, c.IsEssentiallyConstant`,

and dually with `Cone`.  As in mathlib's eventual-constant API, the definitions themselves do not
take `[IsFiltered I]` or `[IsCofiltered I]`; these classes govern the source-facing filtered and
cofiltered specializations, not the stored presentation data or the resulting universal property.
The namespace makes that orientation explicit without repeating `FilteredDiagram` or
`CofilteredDiagram` in every declaration name.
-/

namespace IsFiltered

/-- A filtered-oriented diagram is essentially constant when it admits an essentially constant
cocone. -/
@[stacks 05PV "essentially constant directed systems"]
def IsEssentiallyConstant (M : I ⥤ C) : Prop :=
  ∃ c : Cocone M, c.IsEssentiallyConstant

namespace IsEssentiallyConstant

variable {D : Type uD} [Category.{vD} D]

/-- A diagram indexed by a category with a specified terminal object is essentially constant.
The terminal-index cocone is the canonical presentation. -/
@[stacks 05PU "terminal-index presentation"]
theorem of_isTerminal (M : I ⥤ C) {i : I} (hi : IsTerminal i) :
    IsEssentiallyConstant M := sorry

/-- The selected essentially constant cocone presentation of a filtered-oriented diagram.
This is the single choice boundary for consumers that need presentation data rather than only
the existence predicate. -/
@[stacks 05PV "selected essentially constant cocone"]
noncomputable def cocone {M : I ⥤ C} (hM : IsEssentiallyConstant M) :
    Cocone M :=
  hM.choose

/-- The selected cocone presentation satisfies the defining essential-constancy condition. -/
theorem cocone.isEssentiallyConstant {M : I ⥤ C}
    (hM : IsEssentiallyConstant M) :
    hM.cocone.IsEssentiallyConstant := sorry

/-- The selected stage of an essentially constant filtered diagram. -/
@[stacks 05PU "filtered diagram selected stage"]
noncomputable def cocone.stage {M : I ⥤ C}
    (hM : IsEssentiallyConstant M) : I :=
  hM.choose_spec.choose

/-- The split epimorphism carried by the selected stage of an essentially constant filtered
diagram. -/
@[stacks 05PU "filtered diagram selected split epimorphism"]
noncomputable def cocone.splitEpi {M : I ⥤ C}
    (hM : IsEssentiallyConstant M) :
    SplitEpi (hM.cocone.ι.app (cocone.stage hM)) :=
  hM.choose_spec.choose_spec.choose

/-- The factorization specification for the selected stage of a filtered diagram. -/
@[stacks 05PU "filtered diagram stage factorization"]
theorem cocone.factorization {M : I ⥤ C}
    (hM : IsEssentiallyConstant M) (j : I) :
    ∃ (k : I) (ik : cocone.stage hM ⟶ k) (jk : j ⟶ k),
      M.map jk = hM.cocone.ι.app j ≫ (cocone.splitEpi hM).section_ ≫ M.map ik := sorry

/-- Postcomposition preserves essential constancy of a filtered diagram presentation. -/
theorem map {M : I ⥤ C} (hM : IsEssentiallyConstant M) (F : C ⥤ D) :
    IsEssentiallyConstant (M ⋙ F) := sorry
/- Proof strategy: unpack `hM` as `⟨c, hc⟩`; the required cocone is `F.mapCocone c`, and its
certificate is `hc.map F`. -/

end IsEssentiallyConstant

end IsFiltered

namespace IsCofiltered

/-- A cofiltered-oriented diagram is essentially constant when it admits an essentially constant
cone. -/
@[stacks 05PV "essentially constant directed inverse systems"]
def IsEssentiallyConstant (M : I ⥤ C) : Prop :=
  ∃ c : Cone M, c.IsEssentiallyConstant

/-- A cofiltered diagram presentation is essentially constant exactly when its opposite filtered
presentation is essentially constant. -/
theorem isEssentiallyConstant_iff_op (M : I ⥤ C) :
    IsEssentiallyConstant M ↔ IsFiltered.IsEssentiallyConstant M.op := sorry
/- Proof strategy: send `⟨c, hc⟩` to the opposite cocone `c.op` using
`Cone.isEssentiallyConstant_iff_op`; conversely use `Cocone.unop` and the op/unop involutivity of
cones and cocones. -/

namespace IsEssentiallyConstant

variable {D : Type uD} [Category.{vD} D]

/-- A diagram indexed by a category with a specified initial object is essentially constant.
The initial-index cone is the canonical presentation. -/
@[stacks 05PU "initial-index presentation"]
theorem of_isInitial (M : I ⥤ C) {i : I} (hi : IsInitial i) :
    IsEssentiallyConstant M := sorry

/-- The selected essentially constant cone presentation of a cofiltered-oriented diagram.
This is the single choice boundary for consumers that need presentation data rather than only
the existence predicate. -/
@[stacks 05PV "selected essentially constant cone"]
noncomputable def cone {M : I ⥤ C} (hM : IsEssentiallyConstant M) :
    Cone M :=
  hM.choose

/-- The selected cone presentation satisfies the defining essential-constancy condition. -/
theorem cone.isEssentiallyConstant {M : I ⥤ C}
    (hM : IsEssentiallyConstant M) :
    hM.cone.IsEssentiallyConstant := sorry

/-- The selected stage of an essentially constant cofiltered diagram. -/
@[stacks 05PU "cofiltered diagram selected stage"]
noncomputable def cone.stage {M : I ⥤ C}
    (hM : IsEssentiallyConstant M) : I :=
  hM.choose_spec.choose

/-- The split monomorphism carried by the selected stage of an essentially constant cofiltered
diagram. -/
@[stacks 05PU "cofiltered diagram selected split monomorphism"]
noncomputable def cone.splitMono {M : I ⥤ C}
    (hM : IsEssentiallyConstant M) :
    SplitMono (hM.cone.π.app (cone.stage hM)) :=
  hM.choose_spec.choose_spec.choose

/-- The factorization specification for the selected stage of a cofiltered diagram. -/
@[stacks 05PU "cofiltered diagram stage factorization"]
theorem cone.factorization {M : I ⥤ C}
    (hM : IsEssentiallyConstant M) (j : I) :
    ∃ (k : I) (ki : k ⟶ cone.stage hM) (kj : k ⟶ j),
      M.map kj = M.map ki ≫ (cone.splitMono hM).retraction ≫ hM.cone.π.app j := sorry

/-- Postcomposition preserves essential constancy of a cofiltered diagram presentation. -/
theorem map {M : I ⥤ C} (hM : IsEssentiallyConstant M) (F : C ⥤ D) :
    IsEssentiallyConstant (M ⋙ F) := sorry
/- Proof strategy: unpack `hM` as `⟨c, hc⟩`; use the mapped cone `F.mapCone c` and the certificate
`hc.map F`. -/

end IsEssentiallyConstant

end IsCofiltered

end CategoryTheory


