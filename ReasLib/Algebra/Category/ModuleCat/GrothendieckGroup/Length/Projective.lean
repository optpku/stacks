module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Rank

/-!
# Length and projective rank

This leaf records the comparison square between projective rank, finite-module length, and the
canonical map `K₀(R) → K'_0(R)` over an Artinian local ring.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CategoryTheory.ModuleCat.K0

variable (R : Type u) [CommRing R] [IsArtinianRing R] [IsLocalRing R]

/-
API design: the homomorphism identity is the canonical comparison-square statement, while the
pointwise theorem is a rewrite interface for consumers.  Both retain the module universe `v`:
unlike the local length equivalence, this comparison uses no universe-specific residue-field
generator.  The lower horizontal map remains the standard `AddMonoidHom.mulLeft` construction.
-/

/-- Lemma 10.55.9 (Tag 00JK): length after `K₀(R) → K'_0(R)` is rank followed by
multiplication by the length of `R`. -/
@[stacks 00JK "projective rank and finite-module length comparison"]
theorem finiteLength_comp_projectiveToFinite :
    (finiteLength.{u, v} R).comp (projectiveToFinite.{u, v} R) =
      (AddMonoidHom.mulLeft ((Module.length R R).toNat : ℤ)).comp
        (Projective.rank.{u, v} R) := sorry

/-- Pointwise form of the projective-rank/finite-length comparison square. -/
@[stacks 00JK "projective comparison length evaluation", simp]
theorem finiteLength_projectiveToFinite (x : projective.{u, v} R) :
    finiteLength.{u, v} R (projectiveToFinite.{u, v} R x) =
      ((Module.length R R).toNat : ℤ) * Projective.rank.{u, v} R x := sorry

end CategoryTheory.ModuleCat.K0
