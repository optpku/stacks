module

public import ReasLib.CategoryTheory.Adjunction.Derived.Total.Naturality

@[expose] public section

/-!
# Computation for Total Pointwise-Derived Adjunctions

This file exposes the selected-preimage formula for the total Hom-equivalence and the unit and
counit computations of the resulting adjunction.
-/

open CategoryTheory
open CategoryTheory.MorphismProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction.Total

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  {F : D ⥤ D'} {G : D' ⥤ D}

/-- The forward total Hom-equivalence is the pointwise Hom-equivalence conjugated by the
canonical source-preimage comparisons. -/
@[simp, stacks 09T5]
theorem homEquiv_apply
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    (K : S.Localization) (M : S'.Localization)
    (f : ((G ⋙ S.Q).totalLeftDerived S'.Q S').obj M ⟶ K) :
    homEquiv adj S S' K M f =
      (S'.Q.objObjPreimageIso M).inv ≫
        (Pointwise.homEquiv adj S S' (S.Q.objPreimage K)
          (S'.Q.objPreimage M)).symm
            ((Functor.LeftDerived.Value.totalIso.objPreimage
                (G ⋙ S.Q) S' M).inv ≫
              f ≫ (S.Q.objObjPreimageIso K).inv) ≫
        (Functor.RightDerived.Value.totalIso.objPreimage
          (F ⋙ S'.Q) S K).inv := sorry

/-- The inverse total Hom-equivalence is the inverse pointwise Hom-equivalence conjugated by
the canonical source-preimage comparisons. -/
@[simp, stacks 09T5]
theorem homEquiv_symm_apply
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    (K : S.Localization) (M : S'.Localization)
    (f : M ⟶ ((F ⋙ S'.Q).totalRightDerived S.Q S).obj K) :
    (homEquiv adj S S' K M).symm f =
      (Functor.LeftDerived.Value.totalIso.objPreimage
          (G ⋙ S.Q) S' M).hom ≫
        Pointwise.homEquiv adj S S' (S.Q.objPreimage K)
          (S'.Q.objPreimage M)
            ((S'.Q.objObjPreimageIso M).hom ≫ f ≫
              (Functor.RightDerived.Value.totalIso.objPreimage
                (F ⋙ S'.Q) S K).hom) ≫
        (S.Q.objObjPreimageIso K).hom := sorry

/-- The Hom-equivalence of the total pointwise-derived adjunction is the explicitly assembled
total pointwise-derived Hom-equivalence. -/
@[simp, stacks 09T5]
theorem adjunction_homEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    (K : S.Localization) (M : S'.Localization) :
    (adjunction adj S S').homEquiv M K = homEquiv adj S S' K M := sorry

/-- The unit of the total derived adjunction is obtained by applying its explicit
Hom-equivalence to the identity. -/
@[simp, stacks 09T5]
theorem adjunction_unit_app
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    (M : S'.Localization) :
    (adjunction adj S S').unit.app M =
      homEquiv adj S S'
        (((G ⋙ S.Q).totalLeftDerived S'.Q S').obj M) M (𝟙 _) := sorry

/-- The counit of the total derived adjunction is obtained by applying the inverse explicit
Hom-equivalence to the identity. -/
@[simp, stacks 09T5]
theorem adjunction_counit_app
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S']
    (K : S.Localization) :
    (adjunction adj S S').counit.app K =
      (homEquiv adj S S' K
        (((F ⋙ S'.Q).totalRightDerived S.Q S).obj K)).symm (𝟙 _) := sorry

/-- On a source object, the derived unit is compatible with the original unit after the total
left counit and total right unit are inserted. -/
@[reassoc (attr := simp), stacks 09T5]
theorem adjunction_unit_fac_app
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S'] (X : D') :
    (adjunction adj S S').unit.app (S'.Q.obj X) ≫
        ((F ⋙ S'.Q).totalRightDerived S.Q S).map
          (((G ⋙ S.Q).totalLeftDerivedCounit S'.Q S').app X) =
      S'.Q.map (adj.unit.app X) ≫
        ((F ⋙ S'.Q).totalRightDerivedUnit S.Q S).app (G.obj X) := sorry

/-- On a source object, the derived counit is compatible with the original counit after the
total right unit and total left counit are inserted. -/
@[reassoc (attr := simp), stacks 09T5]
theorem adjunction_counit_fac_app
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    [S.HasLeftCalculusOfFractions] [S'.HasRightCalculusOfFractions]
    [Functor.RightDerived.EverywhereDefined (F ⋙ S'.Q) S]
    [Functor.LeftDerived.EverywhereDefined (G ⋙ S.Q) S'] (X : D) :
    ((G ⋙ S.Q).totalLeftDerived S'.Q S').map
          (((F ⋙ S'.Q).totalRightDerivedUnit S.Q S).app X) ≫
        (adjunction adj S S').counit.app (S.Q.obj X) =
      ((G ⋙ S.Q).totalLeftDerivedCounit S'.Q S').app (F.obj X) ≫
        S.Q.map (adj.counit.app X) := sorry

end CategoryTheory.Adjunction.Total
