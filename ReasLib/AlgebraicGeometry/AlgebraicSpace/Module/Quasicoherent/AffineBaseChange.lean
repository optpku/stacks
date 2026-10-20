module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Qcqs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Affine base change for quasi-coherent modules

The canonical base-change comparison for quasi-coherent modules is invertible along an affine
morphism of algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The canonical base-change map for a quasi-coherent module along an affine morphism of
algebraic spaces is an isomorphism for every cartesian square. -/
instance isIso_baseChange_of_affine {X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_cart : IsPullback g' f' f g) [Affine f] (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((Modules.baseChange h_cart.w).app F) :=
  sorry

/-- Pushforward of a quasi-coherent module along an affine morphism of algebraic spaces commutes
with arbitrary cartesian base change. -/
theorem affineBaseChange_pushforward_isomorphic {X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_cart : IsPullback g' f' f g) [Affine f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIsomorphic ((pullback g).obj ((pushforward f).obj ℱ))
      ((pushforward f').obj ((pullback g').obj ℱ)) :=
  ⟨@asIso _ _ _ _ ((Modules.baseChange h_cart.w).app ℱ)
    (isIso_baseChange_of_affine g' f' f g h_cart ℱ)⟩

end AlgebraicGeometry.AlgebraicSpace.Modules
