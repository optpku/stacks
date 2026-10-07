module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Ample
import StacksCheckRecall

/-!
# Lemma 31.17.4

Descent of an ample invertible module along a finite morphism admitting a norm.

@stack 0BD0
-/

@[expose] public section

universe u

/- Lemma 31.17.4: let `π : X ⟶ Y` be a finite morphism of schemes. If `X` admits an ample
invertible module and `π` admits a norm of degree `d`, then `Y` admits an ample invertible
module. -/
@[stacks 0BD0] #check (
  AlgebraicGeometry.Scheme.hasAmpleInvertibleModule_target_of_finiteMorphismNorm :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ Y) [AlgebraicGeometry.IsFinite π]
      (d : ℕ) (hX : AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X)
      (hnorm : ∃ N : AlgebraicGeometry.Scheme.FiniteMorphismNorm π,
        AlgebraicGeometry.Scheme.IsFiniteMorphismNorm π d N),
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule Y)
