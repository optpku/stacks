module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finite morphism of finite presentation, a quasi-coherent module is of finite
presentation if and only if its pushforward is of finite presentation. -/
theorem isFinitePresentation_iff_pushforward_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ℱ.IsFinitePresentation ↔
      ((Scheme.Modules.pushforward f).obj ℱ).IsFinitePresentation := sorry

/-- Pushforward along a finite morphism of finite presentation preserves finite presentation
for quasi-coherent scheme modules. -/
instance pushforward_obj_isFinitePresentation_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj ℱ).IsFinitePresentation := sorry

end AlgebraicGeometry.Scheme.Modules
