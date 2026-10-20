module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-diagram pointwise limits in functor categories

Mathlib constructs a limit or colimit of a functor-category diagram from the corresponding
pointwise (co)limits.  Its general evaluation comparison API assumes every diagram of the given
shape exists in the target category.  This file exposes the same comparison for one fixed diagram,
under exactly the pointwise instances used by Mathlib's construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w' w v v' u u'

namespace CategoryTheory.Limits.FunctorCategory

variable {J : Type w} [Category.{w'} J]
variable {K : Type u} [Category.{v} K]
variable {C : Type u'} [Category.{v'} C]

namespace evaluation

/-- Evaluation identifies the limit of a fixed functor-category diagram with the limit of its
evaluation, assuming only the pointwise limits needed for this diagram. -/
@[stacks 016Q "evaluation of a fixed pointwise limit"]
noncomputable def limitIso (F : J ⥤ K ⥤ C)
    [∀ k, HasLimit (F.flip.obj k)] (k : K) :
    (limit F).obj k ≅ limit (F ⋙ (evaluation K C).obj k) :=
  preservesLimitIso ((evaluation K C).obj k) F

/-- The fixed-diagram limit comparison commutes with every limit projection. -/
@[reassoc (attr := simp), stacks 016Q "projection from a fixed pointwise limit"]
theorem limitIso.hom_π (F : J ⥤ K ⥤ C)
    [∀ k, HasLimit (F.flip.obj k)] (k : K) (j : J) :
    (limitIso F k).hom ≫ limit.π (F ⋙ (evaluation K C).obj k) j =
      (limit.π F j).app k := sorry

/-- The inverse fixed-diagram limit comparison commutes with every limit projection. -/
@[reassoc (attr := simp), stacks 016Q "inverse projection from a fixed pointwise limit"]
theorem limitIso.inv_π (F : J ⥤ K ⥤ C)
    [∀ k, HasLimit (F.flip.obj k)] (k : K) (j : J) :
    (limitIso F k).inv ≫ (limit.π F j).app k =
      limit.π (F ⋙ (evaluation K C).obj k) j := sorry

/-- Under the fixed-diagram limit comparisons, the structure map of the limit functor is the
map induced by pointwise evaluation. -/
@[reassoc, stacks 016Q "structure map of a fixed pointwise limit"]
theorem limitIso.map (F : J ⥤ K ⥤ C)
    [∀ k, HasLimit (F.flip.obj k)] {k l : K} (h : k ⟶ l) :
    (limit F).map h ≫ (limitIso F l).hom =
      (limitIso F k).hom ≫ limMap (Functor.whiskerLeft F ((evaluation K C).map h)) := sorry

/-- The inverse fixed-diagram limit comparisons are natural in the evaluation object. -/
@[reassoc, stacks 016Q "inverse structure map of a fixed pointwise limit"]
theorem limitIso.inv_map (F : J ⥤ K ⥤ C)
    [∀ k, HasLimit (F.flip.obj k)] {k l : K} (h : k ⟶ l) :
    (limitIso F k).inv ≫ (limit F).map h =
      limMap (Functor.whiskerLeft F ((evaluation K C).map h)) ≫
        (limitIso F l).inv := sorry

/-- Evaluation identifies the colimit of a fixed functor-category diagram with the colimit of its
evaluation, assuming only the pointwise colimits needed for this diagram. -/
@[stacks 016W "evaluation of a fixed pointwise colimit"]
noncomputable def colimitIso (F : J ⥤ K ⥤ C)
    [∀ k, HasColimit (F.flip.obj k)] (k : K) :
    (colimit F).obj k ≅ colimit (F ⋙ (evaluation K C).obj k) :=
  preservesColimitIso ((evaluation K C).obj k) F

/-- Every colimit inclusion commutes with the fixed-diagram colimit comparison. -/
@[reassoc (attr := simp), stacks 016W "inclusion into a fixed pointwise colimit"]
theorem colimitIso.ι_hom (F : J ⥤ K ⥤ C)
    [∀ k, HasColimit (F.flip.obj k)] (k : K) (j : J) :
    (colimit.ι F j).app k ≫ (colimitIso F k).hom =
      colimit.ι (F ⋙ (evaluation K C).obj k) j := sorry

/-- Every colimit inclusion commutes with the inverse fixed-diagram colimit comparison. -/
@[reassoc (attr := simp), stacks 016W "inverse inclusion into a fixed pointwise colimit"]
theorem colimitIso.ι_inv (F : J ⥤ K ⥤ C)
    [∀ k, HasColimit (F.flip.obj k)] (k : K) (j : J) :
    colimit.ι (F ⋙ (evaluation K C).obj k) j ≫ (colimitIso F k).inv =
      (colimit.ι F j).app k := sorry

/-- Under the fixed-diagram colimit comparisons, the structure map of the colimit functor is the
map induced by pointwise evaluation. -/
@[reassoc, stacks 016W "structure map of a fixed pointwise colimit"]
theorem colimitIso.map (F : J ⥤ K ⥤ C)
    [∀ k, HasColimit (F.flip.obj k)] {k l : K} (h : k ⟶ l) :
    (colimit F).map h ≫ (colimitIso F l).hom =
      (colimitIso F k).hom ≫ colimMap (Functor.whiskerLeft F ((evaluation K C).map h)) := sorry

/-- The inverse fixed-diagram colimit comparisons are natural in the evaluation object. -/
@[reassoc, stacks 016W "inverse structure map of a fixed pointwise colimit"]
theorem colimitIso.inv_map (F : J ⥤ K ⥤ C)
    [∀ k, HasColimit (F.flip.obj k)] {k l : K} (h : k ⟶ l) :
    (colimitIso F k).inv ≫ (colimit F).map h =
      colimMap (Functor.whiskerLeft F ((evaluation K C).map h)) ≫
        (colimitIso F l).inv := sorry

end evaluation

end CategoryTheory.Limits.FunctorCategory
