module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 29.25.7 (1): pointwise relative flatness of a quasi-coherent module sheaf is preserved
by arbitrary scheme base change. -/
@[stacks 01U8]
#check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt_pullback_fst :
    ∀ {S X S' : Scheme} (f : X ⟶ S) (g : S' ⟶ S)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (x' : (CategoryTheory.Limits.pullback f g : Scheme.{u}))
      (_ : AlgebraicGeometry.Scheme.Modules.flatOverAt
        ℱ f ((CategoryTheory.Limits.pullback.fst f g).base x')),
      AlgebraicGeometry.Scheme.Modules.flatOverAt
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.fst f g)).obj ℱ)
          (CategoryTheory.Limits.pullback.snd f g) x')

/- Lemma 29.25.7 (2): global relative flatness of a quasi-coherent module sheaf is preserved by
arbitrary scheme base change. -/
@[stacks 01U8]
#check
  (AlgebraicGeometry.Scheme.Modules.flatOver_pullback_fst :
    ∀ {S X S' : Scheme} (f : X ⟶ S) (g : S' ⟶ S)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (_ : AlgebraicGeometry.Scheme.Modules.flatOver ℱ f),
      AlgebraicGeometry.Scheme.Modules.flatOver
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.fst f g)).obj ℱ)
          (CategoryTheory.Limits.pullback.snd f g))
