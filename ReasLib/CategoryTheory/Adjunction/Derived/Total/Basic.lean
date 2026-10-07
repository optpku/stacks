module

public import ReasLib.CategoryTheory.Adjunction.Derived.Pointwise
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Total

@[expose] public section

/-!
# Total Pointwise-Derived Adjunctions

This file owns the Hom-equivalence, core Hom-equivalence, and adjunction obtained by globalizing
the pointwise derived adjunction over localization categories.
-/

open CategoryTheory
open CategoryTheory.MorphismProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction.Total

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  {F : D ⥤ D'} {G : D' ⥤ D}

/-- The canonical Hom-equivalence between the total pointwise left- and right-derived functors
of an adjoint pair. Arbitrary localized objects are reduced to selected source objects, and the
middle equivalence is `Pointwise.homEquiv`. -/
@[stacks 09T5]
noncomputable def homEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    (K : S.Localization) (M : S'.Localization) :
    (((G ⋙ S.Q).totalLeftDerived S'.Q S').obj M ⟶ K) ≃
      (M ⟶ ((F ⋙ S'.Q).totalRightDerived S.Q S).obj K) :=
  ((Functor.LeftDerived.Value.totalIso.objPreimage (G ⋙ S.Q) S' M).homCongr
      (S.Q.objObjPreimageIso K).symm).trans
    ((Pointwise.homEquiv adj S S'
      (S.Q.objPreimage K) (S'.Q.objPreimage M)).symm.trans
        ((S'.Q.objObjPreimageIso M).homCongr
          (Functor.RightDerived.Value.totalIso.objPreimage (F ⋙ S'.Q) S K).symm))

/-- The `CoreHomEquiv` data underlying the total pointwise-derived adjunction.

The field order follows `Adjunction.CoreHomEquiv`: the left-derived localization object comes
first, while `Total.homEquiv` keeps the more convenient `(K, M)` order. -/
@[stacks 09T5]
noncomputable def coreHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S'] :
    Adjunction.CoreHomEquiv
      ((G ⋙ S.Q).totalLeftDerived S'.Q S')
      ((F ⋙ S'.Q).totalRightDerived S.Q S) where
  homEquiv := fun M K ↦ homEquiv adj S S' K M
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- Stacks 09T5: left and right derived functors of an adjoint pair whose pointwise presentations
are essentially constant everywhere are adjoint. This is the canonical total adjunction
assembled from the pointwise Hom-equivalence. -/
@[stacks 09T5]
noncomputable def adjunction
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S'] :
    (G ⋙ S.Q).totalLeftDerived S'.Q S' ⊣
      (F ⋙ S'.Q).totalRightDerived S.Q S :=
  Adjunction.mkOfHomEquiv (coreHomEquiv adj S S')

end CategoryTheory.Adjunction.Total
