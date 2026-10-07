module

public import ReasLib.RingTheory.MvPolynomial.UniversalPolynomialSystem
public import Mathlib.AlgebraicGeometry.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Locus

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme.Hom.FiniteType

noncomputable section

namespace UniversalPolynomialSystem

/-- The coefficient scheme given by the spectrum of the universal coefficient ring. -/
abbrev baseScheme (n d : ℕ) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (CoefficientRing n d))

/-- The universal family scheme given by the spectrum of the quotient coordinate ring. -/
abbrev familyScheme (n d : ℕ) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (CoordinateRing n d))

/-- The morphism from the universal family scheme to its coefficient scheme induced by the
algebra map from the universal coefficient ring to the quotient coordinate ring. -/
def projection (n d : ℕ) : familyScheme n d ⟶ baseScheme n d :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap (CoefficientRing n d) (CoordinateRing n d)))

/-- The open locus of the universal family where the projection is finite type and
quasi-finite at each point. -/
def quasiFiniteOpen (n d : ℕ+) : (familyScheme n d).Opens :=
  quasiFiniteLocus (projection n d)

/-- An open of the universal family is contained in the quasi-finite locus exactly when each
of its points is a point where the universal projection is quasi-finite. -/
theorem le_quasiFiniteOpen_iff (n d : ℕ+) (U : (familyScheme n d).Opens) :
    U ≤ quasiFiniteOpen n d ↔
      ∀ x : familyScheme n d, x ∈ U →
        AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt (projection n d) x := sorry

end UniversalPolynomialSystem
