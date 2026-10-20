module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.RestrictScalars.Homology
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange.Homology
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange.Map.RestrictScalars
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.Homology.Descent

/-!
# Divided powers on homology from coefficient-change covers

Let `X` and `Y` be explicit base-change models of the same divided-power chain DGA, with
coefficient algebras `P` and `S`.  If `R → P` is flat, the original DGA has no positive
homology, and `P → S` is surjective, then coefficient change over `R` is a positive-acyclic
surjective presentation of the restricted target.  Intrinsic homology descent therefore gives
concrete divided powers on its canonical homology algebra.
-/

@[expose] public section

noncomputable section

universe u

namespace DividedPowerChainAlgebra.BaseChange.Descent

variable {R P S : Type u} [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R P] [Algebra R S]
variable {A : DividedPowerChainAlgebra.{u, u} R}

/-- The coefficient-cover model, restricted back to the original base ring. -/
abbrev source (X : BaseChange (R' := P) A) :
    DividedPowerChainAlgebra R :=
  DividedPowerChainAlgebra.restrictScalars (algebraMap R P) X.algebra

/-- The target scalar-extension model, restricted back to the original base ring. -/
abbrev target (Y : BaseChange (R' := S) A) :
    DividedPowerChainAlgebra R :=
  DividedPowerChainAlgebra.restrictScalars (algebraMap R S) Y.algebra

/-- The ordinary divided-power chain-DGA presentation over `R` induced by coefficient change. -/
abbrev map (X : BaseChange (R' := P) A) (sigma : P →ₐ[R] S)
    (Y : BaseChange (R' := S) A) : Hom (source X) (target Y) :=
  X.mapOverBase sigma Y

/-- Flat base change of a positive-acyclic chain DGA remains positive-acyclic after restriction
back to the original base ring. -/
theorem sourcePositiveHomologyVanishes
    (X : BaseChange (R' := P) A) (h_flat : (algebraMap R P).Flat)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes) :
    (source X).toChainDGAlgebra.PositiveHomologyVanishes := sorry

/-- Tag 09PQ: the concrete divided-power graded algebra on homology induced by a flat,
surjective coefficient-change cover. -/
@[stacks 09PQ "divided powers on homology from a coefficient-change cover"]
noncomputable def homologyDPAlgebra
    (X : BaseChange (R' := P) A) (sigma : P →ₐ[R] S)
    (Y : BaseChange (R' := S) A) (h_flat : (algebraMap R P).Flat)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (h_sigma : Function.Surjective sigma) : DividedPowerGradedAlgebra R :=
  (map X sigma Y).homologyDPAlgebra
    (sourcePositiveHomologyVanishes X h_flat hA)
    (X.mapOverBase_surjective sigma Y h_sigma)

/-- The graded algebra underlying coefficient-cover descent is the canonical homology algebra of
the restricted target model. -/
@[simp]
theorem homologyDPAlgebra_toGradedAlgebra
    (X : BaseChange (R' := P) A) (sigma : P →ₐ[R] S)
    (Y : BaseChange (R' := S) A) (h_flat : (algebraMap R P).Flat)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (h_sigma : Function.Surjective sigma) :
    (homologyDPAlgebra X sigma Y h_flat hA h_sigma).toGradedAlgebra =
      (target Y).toChainDGAlgebra.homologyNonnegativePart := sorry

/-- The descended divided powers satisfy the intrinsic target cycle formula. -/
@[simp]
theorem homologyDPAlgebra_gammaPiece
    (X : BaseChange (R' := P) A) (sigma : P →ₐ[R] S)
    (Y : BaseChange (R' := S) A) (h_flat : (algebraMap R P).Flat)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (h_sigma : Function.Surjective sigma) (n d : ℕ)
    (x : (target Y).toChainDGAlgebra.cycles (2 * (d + 1) : ℤ)) :
    (homologyDPAlgebra X sigma Y h_flat hA h_sigma).gamma.gammaPiece n d
        ((target Y).toChainDGAlgebra.homologyπ (2 * (d + 1)) x) =
      (target Y).gammaHomologyClass n d x := sorry

section Independence

variable {Q : Type u} [CommRing Q] [Algebra R Q]

/-- Tag 09PQ: two flat surjective coefficient-change covers of the same target model induce the
same divided-power graded algebra on its homology. -/
@[stacks 09PQ "independence of the coefficient-change cover"]
theorem homologyDPAlgebra_eq
    (X : BaseChange (R' := P) A) (sigma : P →ₐ[R] S)
    (Z : BaseChange (R' := Q) A) (tau : Q →ₐ[R] S)
    (Y : BaseChange (R' := S) A)
    (hP : (algebraMap R P).Flat) (hQ : (algebraMap R Q).Flat)
    (hA : A.toChainDGAlgebra.PositiveHomologyVanishes)
    (h_sigma : Function.Surjective sigma) (h_tau : Function.Surjective tau) :
    homologyDPAlgebra X sigma Y hP hA h_sigma =
      homologyDPAlgebra Z tau Y hQ hA h_tau := sorry

end Independence

end DividedPowerChainAlgebra.BaseChange.Descent
