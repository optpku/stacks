module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

@[expose] public section

open CategoryTheory

universe u

/- Pullback along a morphism of schemes preserves quasicoherence of module sheaves. -/
#check
  (AlgebraicGeometry.Scheme.Modules.pullback_isQuasicoherent :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
      [F.IsQuasicoherent],
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F).IsQuasicoherent)
