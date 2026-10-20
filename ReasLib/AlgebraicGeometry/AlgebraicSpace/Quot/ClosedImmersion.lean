module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.QuasiFinite

/-!
# Closed-immersion pushforward on the Quot functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- Pushforward along a closed immersion of algebraic spaces separated and of finite
presentation over `B` induces a bijection on Quot-points over every scheme over `B`. -/
theorem map_app_bijective (π : X ⟶ Y) (y : Y ⟶ B) [IsClosedImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y]
    (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemeOver B)ᵒᵖ) :
    Function.Bijective ((map π y F).app σ) := sorry

/-- Pushforward along a closed immersion of algebraic spaces separated and of finite
presentation over `B` induces an isomorphism of Quot functors for any quasi-coherent module. -/
@[instance]
theorem isIso_map (π : X ⟶ Y) (y : Y ⟶ B) [IsClosedImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (map π y F) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
