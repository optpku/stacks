/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology
public import stacks_project.Chap82.Lemma_82_26_9_Chow

/-!
# Vanishing of identity bivariant classes

A class in `A^p(X)` is an identity bivariant class in the sense of
`ChowCohomology.degree`: a cap family on Chow groups of good spaces over `X`,
compatible with proper pushforward, flat pullback of fixed relative dimension,
and effective-Cartier Gysin pullback. It vanishes when every cap map is zero.
The source operation `c ∩ [Y]` is the cap of the fundamental class of an
integral algebraic space locally of finite type over `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowCohomology

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable {δ : Points B → ℤ} [IsDimensionFunction δ]
variable {f : X ⟶ B} [QuasiSeparated f] [LocallyOfFiniteType f]

/-- An identity bivariant class vanishes when every cap map is the zero
homomorphism. -/
def Vanishes {p : ℤ} (c : degree δ f p) : Prop :=
  ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ),
    c.cap g k = 0

/-- The zero class vanishes. -/
theorem vanishes_zero (p : ℤ) : Vanishes (zeroCap δ f p) :=
  sorry

/-- An identity bivariant class equals the zero class if and only if it
vanishes. -/
theorem eq_zero_iff_vanishes {p : ℤ} (c : degree δ f p) :
    c = zeroCap δ f p ↔ Vanishes c :=
  sorry

/-- The source-facing operation `c ∩ [Y]` in `CH_{n - p}(Y)`, where
`n = dim_δ(Y)`. -/
def cap_fundamental {Y : AlgebraicSpace S} {p : ℤ} (c : degree δ f p)
    (g : Y ⟶ X) [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [LocallyOfFiniteType g] [IsIntegral Y] :
    (Hom.chowGroup (g ≫ f)) δ ((Hom.deltaDimension (g ≫ f)) δ (univIrreducibleClosed Y) - p) :=
  c.cap g ((Hom.deltaDimension (g ≫ f)) δ (univIrreducibleClosed Y))
    ((Hom.fundamentalClass (g ≫ f)) δ)

/-- `cap_fundamental` is the cap map on the fundamental class of `Y`. -/
theorem cap_fundamental_eq {Y : AlgebraicSpace S} {p : ℤ}
    (c : degree δ f p) (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    [LocallyOfFiniteType g] [IsIntegral Y] :
    cap_fundamental c g =
      c.cap g ((Hom.deltaDimension (g ≫ f)) δ (univIrreducibleClosed Y))
        ((Hom.fundamentalClass (g ≫ f)) δ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChowCohomology
