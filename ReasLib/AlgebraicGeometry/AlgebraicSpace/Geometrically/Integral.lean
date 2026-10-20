module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral

/-!
# Geometric integrality and integral field base changes

Geometric integrality of an algebraic space over a field is equivalent to
integrality after every field extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k]

namespace GeometricallyIntegral

/-- An algebraic space over a field is geometrically integral if and only if
its base change along every field extension is integral. -/
theorem iff_isIntegral_baseChange (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyIntegral X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsIntegral (baseChange (Spec.map (ofHom (algebraMap k K))) X) :=
  sorry

end GeometricallyIntegral

end AlgebraicGeometry.AlgebraicSpace
