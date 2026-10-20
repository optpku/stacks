module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical map between the zero schemes of a section and its pullback along a
locally finite-type morphism is locally of finite type. -/
instance zeroSchemePullbackMap_locallyOfFiniteType
    {X X' : Scheme.{u}} (f : X' ⟶ X) [LocallyOfFiniteType f]
    (ℒ : X.Modules) [Modules.Invertible ℒ] (s : ℒ.sections)
    (h_zeroIdeal : zeroIdealSheaf ((Modules.pullback f).obj ℒ)
      (Modules.sectionsPullback f ℒ s) = (zeroIdealSheaf ℒ s).comap f) :
    LocallyOfFiniteType (zeroSchemePullbackMap f ℒ s h_zeroIdeal) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (zeroSchemePullback_isPullback f ℒ s h_zeroIdeal) inferInstance

end AlgebraicGeometry.Scheme
