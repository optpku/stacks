/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- Import decisions:
-- * `Filtered.Basic` supplies filtered and cofiltered indexing categories.
-- * `RepresentedBy` supplies the universal-element formulation.
-- * `TFAE` is public because the source-facing aggregate criteria use `List.TFAE`.
-- * `Types.Colimits` and `FunctorCategory.Basic` support the Hom-colimit natural
--   transformations.
-- * `EssentiallyConstant.Limits` supplies the canonical (co)limit presentations.
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representability criteria for essentially constant diagrams

For filtered and cofiltered diagrams, essential constancy can be read from the canonical
comparison between a colimit of Hom-presheaves and the Hom-presheaf of a cone vertex. The
source-facing `List.TFAE` results are accompanied by direct equivalences, so applications do not
need to select numbered entries from a TFAE list.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped CategoryTheory

universe uI vI uC vC

namespace CategoryTheory

namespace Limits.Cocone

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]

/-- The canonical comparison `colim_i Hom(-, M.obj i) ⟶ Hom(-, c.pt)` induced by a cocone. -/
noncomputable def comparison {M : I ⥤ C} (c : Cocone M) :
    colimit (M ⋙ uliftYoneda.{uI}) ⟶ uliftYoneda.{uI}.obj c.pt :=
  colimit.desc (M ⋙ uliftYoneda.{uI}) (uliftYoneda.{uI}.mapCocone c)

/-- The Hom-colimit comparison induced by a cocone restricts at each stage to
the corresponding cocone leg after applying the ulifted Yoneda embedding. -/
@[reassoc (attr := simp)]
theorem comparison.ι {M : I ⥤ C} (c : Cocone M) (i : I) :
    colimit.ι (M ⋙ uliftYoneda.{uI}) i ≫ c.comparison =
      (uliftYoneda.{uI}.mapCocone c).ι.app i := sorry

/-- The componentwise form of `Cocone.comparison.ι`. -/
@[reassoc (attr := simp)]
theorem comparison.ι.app {M : I ⥤ C} (c : Cocone M) (i : I)
    (X : Cᵒᵖ) :
    (colimit.ι (M ⋙ uliftYoneda.{uI}) i).app X ≫
        c.comparison.app X =
      ((uliftYoneda.{uI}.mapCocone c).ι.app i).app X := sorry

/-- The Hom-colimit comparisons of two cocones commute with every morphism of cocones. -/
@[reassoc (attr := simp)]
theorem comparison.naturality {M : I ⥤ C} {c d : Cocone M} (f : c ⟶ d) :
    c.comparison ≫ uliftYoneda.{uI}.map f.hom = d.comparison := sorry

end Limits.Cocone

namespace Limits.Cone

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]

/-- The canonical comparison `colim_i Hom(M.obj i, -) ⟶ Hom(c.pt, -)` induced by a cone. -/
noncomputable def comparison {M : I ⥤ C} (c : Cone M) :
    colimit (M.op ⋙ uliftYoneda.{uI}) ⟶
      uliftYoneda.{uI}.obj (Opposite.op c.pt) :=
  colimit.desc (M.op ⋙ uliftYoneda.{uI}) (uliftYoneda.{uI}.mapCocone c.op)

/-- The dual Hom-colimit comparison induced by a cone restricts at each
opposite stage to the corresponding opposite cocone leg. -/
@[reassoc (attr := simp)]
theorem comparison.ι {M : I ⥤ C} (c : Cone M) (i : Iᵒᵖ) :
    colimit.ι (M.op ⋙ uliftYoneda.{uI}) i ≫ c.comparison =
      (uliftYoneda.{uI}.mapCocone c.op).ι.app i := sorry

/-- The componentwise form of `Cone.comparison.ι`. -/
@[reassoc (attr := simp)]
theorem comparison.ι.app {M : I ⥤ C} (c : Cone M) (i : Iᵒᵖ)
    (X : Cᵒᵖᵒᵖ) :
    (colimit.ι (M.op ⋙ uliftYoneda.{uI}) i).app X ≫
        c.comparison.app X =
      ((uliftYoneda.{uI}.mapCocone c.op).ι.app i).app X := sorry

/-- The dual Hom-colimit comparisons of two cones commute with every morphism of cones. -/
@[reassoc (attr := simp)]
theorem comparison.naturality {M : I ⥤ C} {c d : Cone M} (f : c ⟶ d) :
    d.comparison ≫ uliftYoneda.{uI}.map f.hom.op = c.comparison := sorry

end Limits.Cone

namespace IsFiltered

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
variable [IsFiltered I] (M : I ⥤ C)

/-- Lemma 4.22.9 (Stacks 05PY): for a filtered diagram, essential constancy, invertibility of a
Hom-colimit comparison, and existence of a universal stage map are equivalent. -/
@[stacks 05PY]
theorem IsEssentiallyConstant.tfae :
    List.TFAE [
      IsEssentiallyConstant M,
      ∃ c : Cocone M, IsIso c.comparison,
      ∃ c : ColimitCocone M, IsIso c.cocone.comparison,
      ∃ (X : C) (p : StructuredArrow X M),
        (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentedBy
          ((colimit.ι (M ⋙ uliftYoneda.{uI}) p.right).app
            (Opposite.op X) (ULift.up p.hom))] := sorry

/-- A filtered diagram is essentially constant exactly when some cocone has invertible
Hom-colimit comparison. -/
theorem IsEssentiallyConstant.comparison.cocone.iff_exists :
    IsEssentiallyConstant M ↔
      ∃ c : Cocone M, IsIso c.comparison := sorry

/-- A filtered diagram is essentially constant exactly when some colimit cocone has invertible
Hom-colimit comparison. -/
theorem IsEssentiallyConstant.comparison.colimitCocone.iff_exists :
    IsEssentiallyConstant M ↔
      ∃ c : ColimitCocone M, IsIso c.cocone.comparison := sorry

/-- A filtered diagram is essentially constant exactly when a map from some object to one stage
is a universal element of its Hom-colimit presheaf. -/
theorem IsEssentiallyConstant.stageMap.iff_exists :
    IsEssentiallyConstant M ↔
      ∃ (X : C) (p : StructuredArrow X M),
        (colimit (M ⋙ uliftYoneda.{uI})).IsRepresentedBy
          ((colimit.ι (M ⋙ uliftYoneda.{uI}) p.right).app
            (Opposite.op X) (ULift.up p.hom)) := sorry

end IsFiltered

namespace IsCofiltered

variable {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
variable [IsCofiltered I] (M : I ⥤ C)

/-- Lemma 4.22.10 (Stacks 05PZ): for a cofiltered diagram, essential constancy, invertibility of
a dual Hom-colimit comparison, and existence of a universal stage map are equivalent. -/
@[stacks 05PZ]
theorem IsEssentiallyConstant.tfae :
    List.TFAE [
      IsEssentiallyConstant M,
      ∃ c : Cone M, IsIso c.comparison,
      ∃ c : LimitCone M, IsIso c.cone.comparison,
      ∃ (X : C) (p : CostructuredArrow M X),
        (colimit (M.op ⋙ uliftYoneda.{uI})).IsRepresentedBy
          ((colimit.ι (M.op ⋙ uliftYoneda.{uI}) (Opposite.op p.left)).app
            (Opposite.op (Opposite.op X)) (ULift.up p.hom.op))] := sorry

/-- A cofiltered diagram is essentially constant exactly when some cone has invertible
Hom-colimit comparison. -/
theorem IsEssentiallyConstant.comparison.cone.iff_exists :
    IsEssentiallyConstant M ↔
      ∃ c : Cone M, IsIso c.comparison := sorry

/-- A cofiltered diagram is essentially constant exactly when some limit cone has invertible
Hom-colimit comparison. -/
theorem IsEssentiallyConstant.comparison.limitCone.iff_exists :
    IsEssentiallyConstant M ↔
      ∃ c : LimitCone M, IsIso c.cone.comparison := sorry

/-- A cofiltered diagram is essentially constant exactly when a map from one stage to some object
is a universal element of the opposite Hom-colimit presheaf. -/
theorem IsEssentiallyConstant.stageMap.iff_exists :
    IsEssentiallyConstant M ↔
      ∃ (X : C) (p : CostructuredArrow M X),
        (colimit (M.op ⋙ uliftYoneda.{uI})).IsRepresentedBy
          ((colimit.ι (M.op ⋙ uliftYoneda.{uI}) (Opposite.op p.left)).app
            (Opposite.op (Opposite.op X)) (ULift.up p.hom.op)) := sorry

end IsCofiltered

end CategoryTheory
