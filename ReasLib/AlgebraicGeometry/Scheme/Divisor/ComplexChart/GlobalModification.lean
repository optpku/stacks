/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.GlobalGluing
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Decomposition.Derived

/-!
# Source-specific universal property of the displayed global graph modification

The center comparison is the precise alternating-rank, nonzerodivisor and
derived-isomorphism statement of more-algebra.tex, lemma-ideal-well-defined.
It is not equality of arbitrary product ideals or a general claim about graphs
of blowups. New geometric proof debts below concern the already constructed b.
No datum is selected from the universal factorization statement.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors BerthelotOgus
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

/-- The exact source law underlying comparison of two coordinate models.
The existing canonical theorem is admitted; its full hypotheses are retained.
No equality of the uncorrected ideals is asserted. -/
theorem modelDegreeIdeal_powerCorrection {A : Type u} [CommRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    (K L : CochainComplex (ModuleCat A) ℤ)
    [K.IsTermwiseFiniteFree] [L.IsTermwiseFiniteFree]
    (hK : CochainComplex.bounded (ModuleCat A) K)
    (hL : CochainComplex.bounded (ModuleCat A) L)
    (i bK bL : ℤ) (hbK : K.IsStrictlyLE bK) (hbL : L.IsStrictlyLE bL)
    (hKL : IsIsomorphic (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    (m n : ℕ)
    (balance : (m : ℤ) + CochainComplex.BerthelotOgus.Int.DeterminantalIdeal.alternatingRank K i bK =
      (n : ℤ) + CochainComplex.BerthelotOgus.Int.DeterminantalIdeal.alternatingRank L i bL) :
    principalIdeal (f ^ m) * CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal f K i =
      principalIdeal (f ^ n) * CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal f L i :=
  CochainComplex.BerthelotOgus.Int.DeterminantalIdeal.pow_mul_eq_of_isIsomorphic_of_bounded
    f hf i hK hL hbK hbL hKL balance

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)
  [IsEffectiveCartierDivisor D.subschemeι]

/-- The actual pullback ideal, with no selected divisor data. -/
def globalDivisor : (globalW E hE p D).IdealSheafData :=
  D.comap (globalB E hE p D)

/-- The actual complex to which eta must be applied on the global modification. -/
def globalInput : RingedSpace.ModuleDerived (globalW E hE p D).toRingedSpace :=
  (RingedSpace.modulePullbackDerived (globalB E hE p D).toShHom).obj
    ((RingedSpace.modulePullbackDerived p.toShHom).obj E)

/-- The regular divisor remains Cartier on each displayed Rees piece because
its center contains a power of the equation; this property is local on W. -/
theorem globalB_pullbackDefined : D.pullbackDefined (globalB E hE p D) := by
  sorry

/-- Principalization of the actual product center principalizes each factor.
Using base change of the actual degree ideals gives goodness on the displayed
pieces, hence on their gluing. This is a property of this fixed W and b. -/
theorem globalInput_good : IsGoodTriple (globalDivisor E hE p D) (globalInput E hE p D) := by
  sorry

/-- Every competing good triple factors uniquely through the displayed b.
Locally its pullback degree ideals are invertible by the precise power
correction law above (after aligning the Cartier equations by a unit), so
the Rees universal maps agree on overlaps. This Prop theorem is never used
as a choice source to define W, b, Q or T in this component. -/
theorem globalB_lift_unique {Z : Scheme.{u}} (h : Z ⟶ Y)
    (hD : D.pullbackDefined h)
    (hgood : IsGoodTriple (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toShHom).obj
        ((RingedSpace.modulePullbackDerived p.toShHom).obj E))) :
    ExistsUnique fun c : Z ⟶ globalW E hE p D => c ≫ globalB E hE p D = h := by
  sorry

/-- The source's good-triple modification interface, now for the displayed
global construction rather than a selected existence witness. -/
instance globalB_isGoodTripleModification :
    IsGoodTripleModification D ((RingedSpace.modulePullbackDerived p.toShHom).obj E)
      (globalB E hE p D) where
  pullbackDefined := globalB_pullbackDefined E hE p D
  isGoodTriple := globalInput_good E hE p D
  lift_unique h hD hgood := globalB_lift_unique E hE p D h hD hgood

instance globalDivisor_cartier :
    IsEffectiveCartierDivisor (globalDivisor E hE p D).subschemeι :=
  globalB_pullbackDefined E hE p D

theorem globalDivisor_eq : globalDivisor E hE p D = D.comap (globalB E hE p D) := rfl

theorem globalInput_eq : globalInput E hE p D =
    (RingedSpace.modulePullbackDerived (globalB E hE p D).toShHom).obj
      ((RingedSpace.modulePullbackDerived p.toShHom).obj E) := rfl

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
