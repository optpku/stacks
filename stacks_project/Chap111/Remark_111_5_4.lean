module

public import ReasLib.RingTheory.Flat.Projective
public import ReasLib.Geometry.Manifold.Algebra.SmoothFunctions.Flat
import StacksCheckRecall

@[expose] public section

universe u v

open scoped Manifold ContDiff

/- Remark 111.5.4 (1): a finitely presented flat module over a commutative ring is projective. -/
@[stacks 02CT]
 #check (Module.FinitePresentation.projective_of_flat :
  ∀ {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M],
    Module.FinitePresentation A M → Module.Flat A M → Module.Projective A M)

/- Remark 111.5.4 (2): a finite flat non-projective module forces the coefficient ring to be
non-Noetherian. -/
@[stacks 02CT]
 #check (Module.not_isNoetherianRing_of_finite_flat_not_projective :
  ∀ {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Flat A M],
    ¬ Module.Projective A M → ¬ IsNoetherianRing A)

/- Remark 111.5.4 (3): there is a finite flat non-projective module over the ring of `C^∞`
functions on `ℝ`. -/
@[stacks 02CT]
 #check (ContMDiffMap.exists_finite_flat_not_projective_real :
  ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M),
    Module.Finite (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M ∧ Module.Flat (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M ∧
      ¬ Module.Projective (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M)
