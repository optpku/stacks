module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalPolynomialSystem

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace UniversalPolynomialSystem

/-- The universal coefficient scheme is regular for every pair of positive parameters. -/
theorem baseScheme_regular (n d : ℕ+) :
    Scheme.Regular (baseScheme n d) := sorry

/-- The universal coefficient scheme is irreducible for every pair of positive parameters. -/
theorem baseScheme_irreducible (n d : ℕ+) :
    IrreducibleSpace (baseScheme n d) := sorry

/-- The quasi-finite open of the universal family is regular for every pair of positive
parameters. -/
theorem quasiFiniteOpen_regular (n d : ℕ+) :
    Scheme.Regular (quasiFiniteOpen n d).toScheme := sorry

/-- The quasi-finite open of the universal family is irreducible for every pair of positive
parameters. -/
theorem quasiFiniteOpen_irreducible (n d : ℕ+) :
    IrreducibleSpace (quasiFiniteOpen n d).toScheme := sorry

/-- The projection from the quasi-finite open to the universal coefficient scheme is locally
quasi-finite. -/
theorem quasiFiniteOpenProjection_locallyQuasiFinite (n d : ℕ+) :
    LocallyQuasiFinite ((quasiFiniteOpen n d).ι ≫ projection n d) := sorry

/-- The projection from the quasi-finite open to the universal coefficient scheme is syntomic. -/
theorem quasiFiniteOpenProjection_syntomic (n d : ℕ+) :
    Syntomic ((quasiFiniteOpen n d).ι ≫ projection n d) := sorry

/-- For every pair of positive parameters, a dense open of the quasi-finite universal family has
an etale composite morphism to the coefficient scheme. -/
theorem exists_denseOpen_etale (n d : ℕ+) :
    ∃ V : (quasiFiniteOpen n d).toScheme.Opens,
      Dense (V : Set (quasiFiniteOpen n d).toScheme) ∧
        Etale (V.ι ≫ (quasiFiniteOpen n d).ι ≫ projection n d) := sorry

end UniversalPolynomialSystem
