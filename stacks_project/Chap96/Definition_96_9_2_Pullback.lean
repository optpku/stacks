module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.PresheafPullback

/-!
# Presheaf pullback and small étale restriction

The pullback API is owned by the groupoid-fibration library. The small étale
restriction name below preserves the interface used by the sheaf constructions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u a b

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Restriction of a presheaf on `X` to the small étale site of the scheme
underlying `x`, using the canonical selected cartesian evaluation. -/
abbrev restrictEtalePresheaf {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) : (X.p.obj x).left.Etaleᵒᵖ ⥤ A :=
  restrictSmallEtale x F

variable {A : Type a} [Category.{b} A]

#check (AlgebraicGeometry.GroupoidsOver.yonedaEval :
  (x : X.total) → Over (X.p.obj x).left ⥤ X.total)

#check (AlgebraicGeometry.GroupoidsOver.yonedaEval_eq :
  ∀ (x : X.total), yonedaEval x =
    Over.iteratedSliceBackward (X.p.obj x) ⋙
      toFunctor (YonedaSlice.representative (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))))

#check (AlgebraicGeometry.GroupoidsOver.yonedaEval_obj :
  ∀ (x : X.total) (V : Over (X.p.obj x).left),
    (yonedaEval x).obj V =
      (toFunctor (YonedaSlice.representative
        (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x)))).obj
          ((Over.iteratedSliceBackward (X.p.obj x)).obj V))

#check (AlgebraicGeometry.GroupoidsOver.pullbackPresheaf :
  (x : X.total) → (X.totalᵒᵖ ⥤ A) → (Over (X.p.obj x).left)ᵒᵖ ⥤ A)

#check (AlgebraicGeometry.GroupoidsOver.pullbackPresheaf_eq :
  ∀ (x : X.total) (F : X.totalᵒᵖ ⥤ A),
    pullbackPresheaf x F = (presheafInverseImage (yonedaEval x) A).obj F)

#check (AlgebraicGeometry.GroupoidsOver.pullbackPresheaf_obj :
  ∀ (x : X.total) (F : X.totalᵒᵖ ⥤ A) (V : Over (X.p.obj x).left),
    (pullbackPresheaf x F).obj (Opposite.op V) =
      F.obj (Opposite.op ((yonedaEval x).obj V)))

#check (AlgebraicGeometry.GroupoidsOver.pullbackPresheaf_comp_overPostScheme :
  ∀ (x : X.total) (F : X.totalᵒᵖ ⥤ A),
    Nonempty ((Functor.overPostScheme X.p x).op ⋙ pullbackPresheaf x F ≅
      (Over.forget x).op ⋙ F))

#check (AlgebraicGeometry.GroupoidsOver.restrictSmallEtale_eq_pullback :
  ∀ (x : X.total) (F : X.totalᵒᵖ ⥤ A),
    restrictSmallEtale x F =
      (Scheme.Etale.forget (X.p.obj x).left).op ⋙ pullbackPresheaf x F)

#check (AlgebraicGeometry.GroupoidsOver.restrictSmallEtale_obj :
  ∀ (x : X.total) (F : X.totalᵒᵖ ⥤ A) (V' : (X.p.obj x).left.Etale),
    (restrictSmallEtale x F).obj (Opposite.op V') =
      F.obj (Opposite.op ((smallEtaleEval x).obj V')))

end AlgebraicGeometry.GroupoidsOver
