module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction
public import stacks_project.Chap80.Lemma_80_9_1_Descent
public import stacks_project.Chap80.Lemma_80_9_1_Quotient

/-!
# Quotient by a finite locally free subgroupoid

If `(U, R, s, t, c)` is a groupoid scheme over `S` and `P → R` is a monomorphism
making `(U, P, s|_P, t|_P, c|_P)` a groupoid with finite locally free source and
target, monic `j|_P`, affine `U`, and separated locally quasi-finite `j`, then
the fppf quotient `U / P` is an affine scheme and `R` is the restriction of a
groupoid on that quotient.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Lemma 80.9.1 (1): the fppf quotient `U / P` is represented by the affine
scheme `objectQuotient P`. -/
@[stacks 04S4]
theorem objectQuotient_represents {S : Scheme.{u}} (G P : GroupoidScheme S)
    (ι : Hom P G) (hU : P.U = G.U) (h_id : ι.IsIdentityOnObjects hU)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono ι.arrow.left] [Mono P.toPreRelation.hom.left]
    [IsSeparated G.toPreRelation.hom.left]
    [LocallyOfFiniteType G.toPreRelation.hom.left]
    [LocallyQuasiFinite G.toPreRelation.hom.left] :
    IsAffine (objectQuotient P) ∧
      IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ P.toPreRelation
        (StandardTopology.fppf.overTopology S)
        (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
        (objectQuotientMap P) (objectQuotientMap_equalizes P)) := sorry

/-- Lemma 80.9.1 (2): the quotient morphism `U ⟶ Ū` is finite locally free. -/
@[stacks 04S4]
theorem quotientMapOf_isFiniteLocallyFree {S : Scheme.{u}} (G P : GroupoidScheme S)
    (ι : Hom P G) (hU : P.U = G.U) (h_id : ι.IsIdentityOnObjects hU)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono ι.arrow.left] [Mono P.toPreRelation.hom.left]
    [IsSeparated G.toPreRelation.hom.left]
    [LocallyOfFiniteType G.toPreRelation.hom.left]
    [LocallyQuasiFinite G.toPreRelation.hom.left] :
    IsFiniteLocallyFree (quotientMapOf hU).left := sorry

/-- Lemma 80.9.1 (3): `P` is the kernel pair of `U ⟶ Ū`, with `t|_P = pr₀` and
`s|_P = pr₁`. -/
@[stacks 04S4]
theorem subgroupoid_kernelPair_isIso {S : Scheme.{u}} (G P : GroupoidScheme S)
    (ι : Hom P G) (hU : P.U = G.U) (h_id : ι.IsIdentityOnObjects hU)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono ι.arrow.left] [Mono P.toPreRelation.hom.left]
    [IsSeparated G.toPreRelation.hom.left]
    [LocallyOfFiniteType G.toPreRelation.hom.left]
    [LocallyQuasiFinite G.toPreRelation.hom.left] :
    IsIso (P.toPreRelation.kernelPairLift (objectQuotientMap P)
      (objectQuotientMap_equalizes P)) := sorry

/-- Lemma 80.9.1 (4): `R` is the restriction of a groupoid scheme on `Ū` along
the quotient morphism `U ⟶ Ū`. -/
@[stacks 04S4]
theorem exists_isRestriction_objectQuotient {S : Scheme.{u}}
    (G P : GroupoidScheme S) (ι : Hom P G) (hU : P.U = G.U)
    (h_id : ι.IsIdentityOnObjects hU) [IsAffine P.U.left]
    [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono ι.arrow.left] [Mono P.toPreRelation.hom.left]
    [IsSeparated G.toPreRelation.hom.left]
    [LocallyOfFiniteType G.toPreRelation.hom.left]
    [LocallyQuasiFinite G.toPreRelation.hom.left] :
    ∃ (Gbar : GroupoidScheme S) (hUbar : Gbar.U = objectQuotientOver P)
      (φ : Hom G (Gbar.pullback (quotientMapOf hU ≫ eqToHom hUbar.symm))),
      φ.IsIdentityOnObjects rfl ∧ IsIso φ.arrow := sorry

end AlgebraicGeometry.GroupoidScheme
