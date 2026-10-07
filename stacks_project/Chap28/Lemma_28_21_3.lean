module

public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/-!
# Lemma 28.21.3 compatibility entry point

Pullback stability of locally projective quasi-coherent scheme modules is owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Pullback`.
-/

/- Lemma 28.21.3: pullback preserves local projectivity of quasi-coherent scheme modules. -/
@[stacks 060M] #check
  (AlgebraicGeometry.Scheme.Modules.instIsLocallyProjectivePullback :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsQuasicoherent]
      [AlgebraicGeometry.Scheme.Modules.IsLocallyProjective 𝒢],
        AlgebraicGeometry.Scheme.Modules.IsLocallyProjective
          ((Scheme.Modules.pullback f).obj 𝒢))

#check
  (AlgebraicGeometry.Scheme.Modules.IsLocallyProjective.pullback :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {𝒢 : Y.Modules} [𝒢.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.IsLocallyProjective 𝒢 →
        AlgebraicGeometry.Scheme.Modules.IsLocallyProjective
          ((Scheme.Modules.pullback f).obj 𝒢))
