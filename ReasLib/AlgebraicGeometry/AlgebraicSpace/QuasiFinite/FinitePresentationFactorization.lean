module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Finite-presentation factorizations of quasi-finite morphisms of algebraic spaces

A quasi-finite separated morphism locally of finite presentation, with
quasi-compact, absolutely quasi-separated target, factors as a quasi-compact
open immersion followed by a finite morphism of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A quasi-finite separated morphism of algebraic spaces over a scheme, locally
of finite presentation and with quasi-compact, absolutely quasi-separated target,
factors as a quasi-compact open immersion followed by a finite morphism of finite
presentation. -/
@[stacks 0874]
theorem QuasiFinite.exists_openImmersion_finitePresentationFactorization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] [LocallyOfFinitePresentation f]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    ∃ (T : AlgebraicSpace S) (j : X ⟶ T) (π : T ⟶ Y),
      QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧
        FinitePresentation π ∧ j ≫ π = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
