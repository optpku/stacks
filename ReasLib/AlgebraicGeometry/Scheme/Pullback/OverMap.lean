module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Maps between base changes of schemes

A morphism of schemes over a base induces a morphism between their base changes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Pullback

/-- Base change sends a morphism `X ⟶ Y` over `S` to the induced morphism
`X ×_S S' ⟶ Y ×_S S'`. -/
noncomputable abbrev overMap {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) :
    (pullback (f ≫ p) g : Scheme) ⟶ pullback p g :=
  ((Over.pullback g).map (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p)).left

/-- The induced morphism between base changes commutes with the projection to
the new base. -/
theorem overMap_comp_snd {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) :
    overMap g p f ≫ pullback.snd p g = pullback.snd (f ≫ p) g :=
  Over.w ((Over.pullback g).map (Over.homMk f : Over.mk (f ≫ p) ⟶ Over.mk p))

/-- The structure morphism of the base-changed source is locally of finite type
if its original structure morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeOverMapComp {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType (f ≫ p)] :
    LocallyOfFiniteType (overMap g p f ≫ pullback.snd p g) := by
  rw [overMap_comp_snd]
  infer_instance

/-- The square formed by a morphism, its base change, and the projections to
the original schemes is cartesian. -/
theorem isPullback_overMap {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) :
    IsPullback (pullback.fst (f ≫ p) g) (overMap g p f) f
      (pullback.fst p g) :=
  sorry

/-- The induced morphism between base changes is locally of finite type if the
original morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeOverMap {S S' X Y : Scheme.{u}}
    (g : S' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (overMap g p f) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (isPullback_overMap g p f) inferInstance

end AlgebraicGeometry.Scheme.Pullback
