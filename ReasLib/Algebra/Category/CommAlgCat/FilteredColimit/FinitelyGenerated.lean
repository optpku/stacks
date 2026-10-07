module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finitely generated subalgebras of filtered colimits

This leaf records the finite-presentation consequence needed to descend a finitely generated
subalgebra of a filtered colimit of commutative algebras over an arbitrary commutative base ring
to one stage of the diagram.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CommAlgCat

variable {k : Type u} {I : Type v} [CommRing k] [Category I] [IsFiltered I]

/-- A finitely generated `k`-subalgebra of a filtered colimit is already represented at one
stage: its inclusion into the colimit is the composite of a stage map and the canonical cocone
map. This factorization is the primary finite-stage API. -/
@[stacks 037N "filtered-colimit finite-stage factorization spec"]
theorem exists_fg_subalgebra_factorization
    (F : I ⥤ CommAlgCat.{u} k) [HasColimit F]
    (T : Subalgebra k (colimit F : CommAlgCat.{u} k)) (hT : T.FG) :
    ∃ (i : I) (φ : T →ₐ[k] F.obj i),
      (colimit.ι F i).hom.comp φ = T.val := sorry

/-- A finitely generated `k`-subalgebra of a filtered colimit of commutative `k`-algebras
admits an injective map to one stage of the diagram. -/
@[stacks 037N "filtered-colimit finite-stage factorization"]
theorem exists_injective_stage_of_fg_subalgebra_colimit
    (F : I ⥤ CommAlgCat.{u} k) [HasColimit F]
    (T : Subalgebra k (colimit F : CommAlgCat.{u} k)) (hT : T.FG) :
    ∃ (i : I) (φ : T →ₐ[k] F.obj i), Function.Injective φ := sorry

end CommAlgCat
