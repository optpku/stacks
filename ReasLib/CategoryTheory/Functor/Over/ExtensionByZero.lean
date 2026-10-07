module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

noncomputable section

namespace CategoryTheory.Over.Forget.LeftKanExtension

variable {C : Type u} [Category.{v} C]

/-- The canonical map from the value on a slice object to the value of the left Kan extension
along the forgetful functor. -/
noncomputable def extensionByZeroSummand
    (U : C) (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
    [((Over.forget U).op).HasLeftKanExtension F]
    (V : C) (φ : V ⟶ U) :
    F.obj (op (Over.mk φ)) ⟶
      ((Over.forget U).op.leftKanExtension F).obj (op V) :=
  ((Over.forget U).op.leftKanExtensionUnit F).app (op (Over.mk φ))

/-- The canonical morphism from the coproduct of the slice values indexed by arrows `V ⟶ U`
to the value at `V` of the left Kan extension along the forgetful functor. -/
noncomputable def extensionByZeroCoproductMap
    (U : C) (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
    [((Over.forget U).op).HasPointwiseLeftKanExtension F]
    (V : C) :
    (∐ fun φ : V ⟶ U ↦ F.obj (op (Over.mk φ))) ⟶
      ((Over.forget U).op.leftKanExtension F).obj (op V) :=
  Sigma.desc (extensionByZeroSummand U F V)

/-- The coproduct morphism identifies the direct sum of the slice values indexed by arrows
`V ⟶ U` with the value at `V` of the pointwise left Kan extension. -/
@[instance]
theorem extensionByZeroCoproductMap_isIso
    (U : C) (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{max u v w})
    [((Over.forget U).op).HasPointwiseLeftKanExtension F]
    (V : C) :
    IsIso (extensionByZeroCoproductMap U F V) := sorry

end CategoryTheory.Over.Forget.LeftKanExtension
