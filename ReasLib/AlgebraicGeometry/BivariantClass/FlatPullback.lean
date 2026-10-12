/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.BaseChange
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Composition
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.FlatPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The cap family given by flat pullback along every displayed cartesian base change
of a flat morphism of relative dimension `r`. -/
noncomputable def flatPullbackCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] :
    CapFamily δ f (-(r : ℤ)) :=
  fun {X' Y'} _ _ _ f' _ _ square k ↦
    (AddEquiv.toAddMonoidHom
      (@AddEquiv.cast ℤ (fun n : ℤ ↦ RelativeChow δ X' n) inferInstance
        (k + (r : ℤ)) (k - (-(r : ℤ))) (sub_neg_eq_add k (r : ℤ)).symm)).comp
      (@ChowGroup.flatPullback S _ δ _ X' Y' _ _ f' r
        (MorphismProperty.IsStableUnderBaseChange.of_isPullback square inferInstance)
        ((Scheme.Hom.instRelativeDimensionIsStableUnderBaseChange r).of_isPullback
          square inferInstance) k)

/-- Evaluating `flatPullbackCap` is the base-changed Chow flat-pullback map, transported
to the grading of a degree-`-r` class. -/
theorem flatPullbackCap_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left)
    (k : ℤ) (α : RelativeChow δ Y' k) :
    flatPullbackCap δ f r i f' g square k α =
      @AddEquiv.cast ℤ (fun n : ℤ ↦ RelativeChow δ X' n) inferInstance
        (k + (r : ℤ)) (k - (-(r : ℤ))) (sub_neg_eq_add k (r : ℤ)).symm
        (@ChowGroup.flatPullback S _ δ _ X' Y' _ _ f' r
          (MorphismProperty.IsStableUnderBaseChange.of_isPullback square inferInstance)
          ((Scheme.Hom.instRelativeDimensionIsStableUnderBaseChange r).of_isPullback
            square inferInstance) k α) := sorry

/-- Base-changed flat-pullback cap maps commute with proper pushforward. -/
theorem flatPullbackCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] :
    CompatibleWithProperPushforward δ (flatPullbackCap δ f r) := sorry

/-- Base-changed flat-pullback cap maps commute with further flat pullback. -/
theorem flatPullbackCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] :
    CompatibleWithFlatPullback δ (flatPullbackCap δ f r) := sorry

/-- Base-changed flat-pullback cap maps commute with effective-Cartier Gysin pullback. -/
theorem flatPullbackCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] :
    CompatibleWithCartierGysin δ (flatPullbackCap δ f r) := sorry

/-- The degree-`-r` bivariant class defined by flat pullback along a flat morphism of
relative dimension `r`. -/
noncomputable def flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] :
    AlgebraicGeometry.BivariantClass δ f (-(r : ℤ)) where
  cap := flatPullbackCap δ f r
  map_proper := flatPullbackCap_mapProper δ f r
  pullback_flat := flatPullbackCap_pullbackFlat δ f r
  gysin_cartier := flatPullbackCap_gysinCartier δ f r

/-- The cap family of `flatPullback` is `flatPullbackCap`. -/
theorem flatPullback_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r] :
    ((flatPullback δ f r).cap : CapFamily δ f (-(r : ℤ))) =
      (flatPullbackCap δ f r : CapFamily δ f (-(r : ℤ))) := sorry

/-- The cap action of `flatPullback` on a displayed base change is the corresponding
Chow flat-pullback map, with the canonical degree transport. -/
theorem flatPullback_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left)
    (k : ℤ) (α : RelativeChow δ Y' k) :
    (flatPullback δ f r).cap i f' g square k α =
      @AddEquiv.cast ℤ (fun n : ℤ ↦ RelativeChow δ X' n) inferInstance
        (k + (r : ℤ)) (k - (-(r : ℤ))) (sub_neg_eq_add k (r : ℤ)).symm
        (@ChowGroup.flatPullback S _ δ _ X' Y' _ _ f' r
          (MorphismProperty.IsStableUnderBaseChange.of_isPullback square inferInstance)
          ((Scheme.Hom.instRelativeDimensionIsStableUnderBaseChange r).of_isPullback
            square inferInstance) k α) := sorry

end AlgebraicGeometry.BivariantClass
