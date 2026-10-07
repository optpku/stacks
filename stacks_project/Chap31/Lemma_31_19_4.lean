module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Map.BaseChange

open CategoryTheory Limits

universe u

/- Lemma 31.19.4: in a cartesian square of schemes with immersion sides, every homogeneous
component of the canonical conormal-algebra comparison is an epimorphism. -/
@[stacks 0635] #check
  (AlgebraicGeometry.Scheme.ConormalAlgebra.map_component_epi_of_isPullback :
    ∀ {Z X Z' X' : AlgebraicGeometry.Scheme.{u}}
      {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
      [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.IsImmersion i'],
      (sq : IsPullback f i i' g) → (n : ℕ) →
        Epi ((AlgebraicGeometry.Scheme.ConormalAlgebra.map sq.toCommSq).hom n))

/- Under flat base change, the canonical bundled conormal-algebra comparison is an
isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.ConormalAlgebra.map_isIso_of_isPullback_of_flat :
    ∀ {Z X Z' X' : AlgebraicGeometry.Scheme.{u}}
      {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}
      [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.IsImmersion i']
      [AlgebraicGeometry.Flat g],
      (sq : IsPullback f i i' g) →
        IsIso (C := SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} Z.sheaf ℕ)
          (AlgebraicGeometry.Scheme.ConormalAlgebra.map sq.toCommSq))
