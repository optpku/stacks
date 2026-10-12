/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.FinitePartDecomposition
public import ReasLib.RingTheory.Etale.Neighborhood
public import ReasLib.RingTheory.LocalRing.Product
public import ReasLib.RingTheory.QuasiFinite.FiniteType

@[expose] public section

/-!
# Criteria for henselian local rings

This leaf records the factorization, etale-neighborhood, finite-algebra, and
finite-type splitting formulations of henselianity.  It deliberately uses the
neutral owners for neighborhoods, local-product decompositions, fibers, and
finite-part decompositions.  The source-facing 04GG aggregate is retained as a
`List.TFAE`, while named equivalences are the intended downstream interface.

The aggregate criteria quantify target algebras in the universe of the base
ring.  A proposition cannot itself quantify over arbitrary Lean universe
levels; the source-universe-polymorphic outcome theorems below carry the
target universe explicitly.
-/

universe u v

open IsLocalRing Polynomial

namespace HenselianLocalRing.Criteria

variable (R : Type u) [CommRing R] [IsLocalRing R]

namespace Root

/-- Stacks Lemma 10.153.3 (tag `04GG`): every simple root of an arbitrary
residue polynomial lifts to a root over the local ring. -/
@[stacks 04GG "arbitrary simple-root lifting"]
def simpleLift : Prop :=
  ∀ f : R[X], ∀ a : ResidueField R,
    aeval a f = 0 →
    aeval a f.derivative ≠ 0 →
    ∃ x : R, f.IsRoot x ∧ residue R x = a

end Root

namespace Factorization

/-- Stacks Lemma 10.153.3 (tag `04GG`): coprime factorizations of monic
residue polynomials lift to factorizations of the original monic polynomial. -/
@[stacks 04GG "monic coprime factorization lifting"]
def monicCoprimeLift : Prop :=
  ∀ f : R[X], f.Monic →
    ∀ g h : (ResidueField R)[X],
      f.map (residue R) = g * h →
      IsCoprime g h →
      ∃ g' h' : R[X],
        f = g' * h' ∧
        g'.map (residue R) = g ∧
        h'.map (residue R) = h

/-- Stacks Lemma 10.153.3 (tag `04GG`): monic coprime factorization lifting
can preserve the degree of the selected factor. -/
@[stacks 04GG "monic coprime factorization lifting with degree"]
def monicCoprimeLiftWithDegree : Prop :=
  ∀ f : R[X], f.Monic →
    ∀ g h : (ResidueField R)[X],
      f.map (residue R) = g * h →
      IsCoprime g h →
      ∃ g' h' : R[X],
        f = g' * h' ∧
        g'.map (residue R) = g ∧
        h'.map (residue R) = h ∧
        g'.natDegree = g.natDegree

/-- Stacks Lemma 10.153.3 (tag `04GG`): coprime factorizations of arbitrary
residue polynomials lift to factorizations over the local ring. -/
@[stacks 04GG "coprime factorization lifting"]
def coprimeLift : Prop :=
  ∀ f : R[X],
    ∀ g h : (ResidueField R)[X],
      f.map (residue R) = g * h →
      IsCoprime g h →
      ∃ g' h' : R[X],
        f = g' * h' ∧
        g'.map (residue R) = g ∧
        h'.map (residue R) = h

/-- Stacks Lemma 10.153.3 (tag `04GG`): arbitrary coprime factorization
lifting can preserve the degree of a selected nonzero residue factor. -/
@[stacks 04GG "coprime factorization lifting with degree"]
def coprimeLiftWithDegree : Prop :=
  ∀ f : R[X],
    ∀ g h : (ResidueField R)[X],
      g ≠ 0 →
      f.map (residue R) = g * h →
      IsCoprime g h →
      ∃ g' h' : R[X],
        f = g' * h' ∧
        g'.map (residue R) = g ∧
        h'.map (residue R) = h ∧
        g'.degree = g.degree

end Factorization

namespace Etale

/-- Stacks Lemma 10.153.3 (tag `04GG`): every etale neighborhood of the
closed point with unchanged residue field admits a retraction to `R`. -/
@[stacks 04GG "etale neighborhood retraction"]
def hasRetraction : Prop :=
  ∀ U : PrimeSpectrum.EtaleNeighborhood.{u, u} (closedPoint R),
    Nonempty (U.carrier →ₐ[R] R)

/-- Stacks Lemma 10.153.3 (tag `04GG`): an etale-neighborhood retraction is
unique when it pulls the maximal ideal back to the selected point. -/
@[stacks 04GG "unique etale neighborhood retraction"]
def hasUniqueRetraction : Prop :=
  ∀ U : PrimeSpectrum.EtaleNeighborhood.{u, u} (closedPoint R),
    ∃! τ : U.carrier →ₐ[R] R,
      U.point.asIdeal = Ideal.comap τ.toRingHom (maximalIdeal R)

end Etale

namespace Finite

/-- Stacks Lemma 10.153.3 (tag `04GG`): every module-finite algebra over `R`
is a product of local rings. -/
@[stacks 04GG "finite algebra local-product criterion"]
def localProduct : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
    IsLocalRing.isProduct S

/-- Stacks Lemma 10.153.3 (tag `04GG`): every module-finite algebra over `R`
is a finite product of local rings. -/
@[stacks 04GG "finite algebra finite-local-product criterion"]
def finiteLocalProduct : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S],
    IsLocalRing.isFiniteProduct S

end Finite

namespace FiniteType

/-- Stacks Lemma 10.153.3 (tag `04GG`): every finite-type algebra over `R`
splits into a module-finite part and a remainder with no quasi-finite point
over the closed point. -/
@[stacks 04GG "finite-type splitting without quasi-finite points"]
def splitFiniteNonQuasiFinite : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
    ∃ D : Algebra.FinitePartDecomposition R S,
      D.noQuasiFinitePoints (closedPoint R)

/-- Stacks Lemma 10.153.3 (tag `04GG`): every finite-type algebra over `R`
splits into a module-finite part and a remainder with positive-dimensional
minimal-prime components in the closed fiber. -/
@[stacks 04GG "finite-type splitting with positive-dimensional fiber"]
def splitFinitePositiveFiber : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S],
    ∃ D : Algebra.FinitePartDecomposition R S,
      D.positiveDimensionalFiber (closedPoint R)

end FiniteType

namespace QuasiFinite

/-- Stacks Lemma 10.153.3 (tag `04GG`): every finite-type quasi-finite
algebra over `R` splits into a module-finite part and a remainder with
subsingleton closed fiber. -/
@[stacks 04GG "quasi-finite splitting with zero fiber"]
def splitFiniteZeroFiber : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S],
    Algebra.FiniteType.QuasiFinite R S →
      ∃ D : Algebra.FinitePartDecomposition R S,
        D.subsingletonFiber (closedPoint R)

end QuasiFinite

/-- Stacks Lemma 10.153.3 (tag `04GG`): henselianity, arbitrary simple-root
lifting, coprime-factorization lifting, etale-neighborhood retractions, and
the finite and finite-type splitting criteria are equivalent. -/
@[stacks 04GG "henselian local ring criteria"]
theorem tfae :
    List.TFAE
      [ HenselianLocalRing R
      , Root.simpleLift R
      , Factorization.monicCoprimeLift R
      , Factorization.monicCoprimeLiftWithDegree R
      , Factorization.coprimeLift R
      , Factorization.coprimeLiftWithDegree R
      , Etale.hasRetraction R
      , Etale.hasUniqueRetraction R
      , Finite.localProduct R
      , Finite.finiteLocalProduct R
      , FiniteType.splitFiniteNonQuasiFinite R
      , FiniteType.splitFinitePositiveFiber R
      , QuasiFinite.splitFiniteZeroFiber R
      ] := sorry

namespace Root

/-- The arbitrary simple-root lifting criterion is equivalent to henselianity. -/
@[stacks 04GG "henselianity and arbitrary simple-root lifting"]
theorem henselian_iff_simpleLift :
    HenselianLocalRing R ↔ simpleLift R := sorry

end Root

namespace Factorization

/-- The monic coprime-factorization lifting criterion is equivalent to
henselianity. -/
@[stacks 04GG "henselianity and monic coprime factorization lifting"]
theorem henselian_iff_monicCoprimeLift :
    HenselianLocalRing R ↔ monicCoprimeLift R := sorry

/-- The degree-preserving monic coprime-factorization lifting criterion is
equivalent to henselianity. -/
@[stacks 04GG "henselianity and monic coprime factorization lifting with degree"]
theorem henselian_iff_monicCoprimeLiftWithDegree :
    HenselianLocalRing R ↔ monicCoprimeLiftWithDegree R := sorry

/-- The arbitrary coprime-factorization lifting criterion is equivalent to
henselianity. -/
@[stacks 04GG "henselianity and coprime factorization lifting"]
theorem henselian_iff_coprimeLift :
    HenselianLocalRing R ↔ coprimeLift R := sorry

/-- The degree-preserving arbitrary coprime-factorization lifting criterion
is equivalent to henselianity. -/
@[stacks 04GG "henselianity and coprime factorization lifting with degree"]
theorem henselian_iff_coprimeLiftWithDegree :
    HenselianLocalRing R ↔ coprimeLiftWithDegree R := sorry

end Factorization

namespace Etale

/-- The etale-neighborhood retraction criterion is equivalent to henselianity. -/
@[stacks 04GG "henselianity and etale neighborhood retractions"]
theorem henselian_iff_hasRetraction :
    HenselianLocalRing R ↔ hasRetraction R := sorry

/-- The unique etale-neighborhood retraction criterion is equivalent to
henselianity. -/
@[stacks 04GG "henselianity and unique etale neighborhood retractions"]
theorem henselian_iff_hasUniqueRetraction :
    HenselianLocalRing R ↔ hasUniqueRetraction R := sorry

end Etale

namespace Finite

/-- The local-product criterion for finite algebras is equivalent to
henselianity. -/
@[stacks 04GG "henselianity and finite algebra local products"]
theorem henselian_iff_localProduct :
    HenselianLocalRing R ↔ localProduct R := sorry

/-- The finite-local-product criterion for finite algebras is equivalent to
henselianity. -/
@[stacks 04GG "henselianity and finite algebra finite local products"]
theorem henselian_iff_finiteLocalProduct :
    HenselianLocalRing R ↔ finiteLocalProduct R := sorry

end Finite

namespace FiniteType

/-- The finite-type splitting criterion with no quasi-finite closed-fiber
points is equivalent to henselianity. -/
@[stacks 04GG "henselianity and finite-type non-quasi-finite splitting"]
theorem henselian_iff_splitFiniteNonQuasiFinite :
    HenselianLocalRing R ↔ splitFiniteNonQuasiFinite R := sorry

omit [IsLocalRing R] in
/-- A henselian local base splits any finite-type algebra into a module-finite
part and a residual source-universe algebra without quasi-finite points over
the closed point. -/
@[stacks 04GG "finite-type non-quasi-finite split from henselianity"]
theorem existsNonQuasiFiniteSplit_of_henselian
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [HenselianLocalRing R] :
    ∃ D : Algebra.FinitePartDecomposition R S,
      D.noQuasiFinitePoints
        (@IsLocalRing.closedPoint R _ HenselianLocalRing.toIsLocalRing) := sorry

/-- The finite-type splitting criterion with positive-dimensional closed
fiber is equivalent to henselianity. -/
@[stacks 04GG "henselianity and finite-type positive-fiber splitting"]
theorem henselian_iff_splitFinitePositiveFiber :
    HenselianLocalRing R ↔ splitFinitePositiveFiber R := sorry

omit [IsLocalRing R] in
/-- A henselian local base splits any finite-type algebra into a module-finite
part and a residual algebra whose closed fiber has positive-dimensional
minimal-prime components. -/
@[stacks 04GG "finite-type positive-fiber split from henselianity"]
theorem existsPositiveFiberSplit_of_henselian
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [HenselianLocalRing R] :
    ∃ D : Algebra.FinitePartDecomposition R S,
      D.positiveDimensionalFiber
        (@IsLocalRing.closedPoint R _ HenselianLocalRing.toIsLocalRing) := sorry

end FiniteType

namespace QuasiFinite

/-- The quasi-finite splitting criterion with subsingleton closed fiber is
equivalent to henselianity. -/
@[stacks 04GG "henselianity and quasi-finite zero-fiber splitting"]
theorem henselian_iff_splitFiniteZeroFiber :
    HenselianLocalRing R ↔ splitFiniteZeroFiber R := sorry

omit [IsLocalRing R] in
/-- A henselian local base splits a finite-type quasi-finite algebra into a
module-finite part and a residual algebra with subsingleton closed fiber. -/
@[stacks 04GG "quasi-finite zero-fiber split from henselianity"]
theorem existsZeroFiberSplit_of_henselian
    {S : Type v} [CommRing S] [Algebra R S]
    [HenselianLocalRing R] (hquasiFinite : Algebra.FiniteType.QuasiFinite R S) :
    ∃ D : Algebra.FinitePartDecomposition R S,
      D.subsingletonFiber
        (@IsLocalRing.closedPoint R _ HenselianLocalRing.toIsLocalRing) := sorry

end QuasiFinite

end HenselianLocalRing.Criteria
