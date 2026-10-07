module

public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.FirstChern.Relative

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The cap family obtained by intersecting with the first Chern class of the pullback
of an invertible module. -/
noncomputable def firstChernCap (ℒ : X.Modules) [hℒ : Scheme.Modules.Invertible ℒ] :
    BivariantClass.CapFamily δ (𝟙 (Over.mk p)) 1 :=
  fun {X' _} _ _ i f' g _ square k ↦
    (@ChowGroup.firstChernClassCap S _ δ _ X' _
      ((Scheme.Modules.pullback i.left).obj ℒ)
      (Scheme.Modules.Invertible.pullback i.left hℒ) k).comp
        ((castDegree δ (Int.sub_zero k)).comp
          (identityCap δ p i f' g square k))

/-- First-Chern intersection commutes with proper pushforward. -/
theorem firstChernMapProper (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    BivariantClass.CompatibleWithProperPushforward δ (firstChernCap δ p ℒ) := sorry

/-- First-Chern intersection commutes with flat pullback. -/
theorem firstChernPullbackFlat (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    BivariantClass.CompatibleWithFlatPullback δ (firstChernCap δ p ℒ) := sorry

/-- First-Chern intersection commutes with effective-Cartier Gysin pullback. -/
theorem firstChernGysinCartier (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    BivariantClass.CompatibleWithCartierGysin δ (firstChernCap δ p ℒ) := sorry

/-- The degree-one Chow-cohomology class defined by an invertible module. -/
noncomputable def firstChernClass (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] :
    degree δ p 1 where
  cap := firstChernCap δ p ℒ
  map_proper := firstChernMapProper δ p ℒ
  pullback_flat := firstChernPullbackFlat δ p ℒ
  gysin_cartier := firstChernGysinCartier δ p ℒ

/-- The cap family of `firstChernClass` is `firstChernCap`. -/
theorem firstChernClass_cap (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ Over.mk p) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk p)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (𝟙 X) g.left) (k : ℤ) :
    (firstChernClass δ p ℒ).cap i f' g square k =
      firstChernCap δ p ℒ i f' g square k := sorry

/-- On the canonical identity square, `firstChernClass` acts by intersection with the
first Chern class of the pulled-back invertible module. -/
theorem firstChernClass_apply (ℒ : X.Modules) [hℒ : Scheme.Modules.Invertible ℒ]
    {X' : Over S} [LocallyOfFiniteType X'.hom] (f : X' ⟶ Over.mk p)
    (k : ℤ) (α : RelativeChow δ X' k) :
    (firstChernClass δ p ℒ).cap f (𝟙 X') f IsPullback.of_id_snd k α =
      @ChowGroup.firstChernClassCap S _ δ _ X' _
        ((Scheme.Modules.pullback f.left).obj ℒ)
        (Scheme.Modules.Invertible.pullback f.left hℒ) k α := sorry

end AlgebraicGeometry.ChowCohomology
