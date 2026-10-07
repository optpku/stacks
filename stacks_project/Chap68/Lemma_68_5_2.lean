module

public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap68.Lemma_68_5_1_PropertyAlpha
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable

/-!
# Zariski locality of conditions on algebraic spaces

If `P` is one of the properties (α), (β), (γ), (δ), (ε), (ζ), or (θ) of
algebraic spaces from Lemma 68.5.1, and `X = ⋃ 𝒰.X i` is a Zariski open
covering with each `𝒰.X i` satisfying `P`, then `X` satisfies `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasPropertyAlpha

/-- Lemma 68.5.2 (1): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` has property (α),
then `X` has property (α). -/
@[stacks 03KE]
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, HasPropertyAlpha (𝒰.X i)] : HasPropertyAlpha X :=
  sorry

end HasPropertyAlpha

namespace HasPropertyBeta

/-- Lemma 68.5.2 (2): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` has property (β),
then `X` has property (β). -/
@[stacks 03KE]
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, HasPropertyBeta (𝒰.X i)] : HasPropertyBeta X :=
  sorry

end HasPropertyBeta

namespace IsDecent

/-- Lemma 68.5.2 (3): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is decent
(property (γ)), then `X` is decent. -/
@[stacks 03KE]
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsDecent (𝒰.X i)] : IsDecent X :=
  sorry

end IsDecent

namespace IsReasonable

/-- Lemma 68.5.2 (4): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is reasonable
(property (δ)), then `X` is reasonable. -/
@[stacks 03KE]
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsReasonable (𝒰.X i)] : IsReasonable X :=
  sorry

end IsReasonable

namespace IsVeryReasonable

/-- Lemma 68.5.2 (5): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is very reasonable
(property (ε)), then `X` is very reasonable. -/
@[stacks 03KE]
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsVeryReasonable (𝒰.X i)] : IsVeryReasonable X :=
  sorry

end IsVeryReasonable

namespace IsAbsolutelyZariskiLocallyQuasiSeparated

/-- Lemma 68.5.2 (6): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is absolutely
Zariski locally quasi-separated (property (ζ)), then `X` is absolutely Zariski
locally quasi-separated. -/
@[stacks 03KE]
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsAbsolutelyZariskiLocallyQuasiSeparated (𝒰.X i)] :
    IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  sorry

end IsAbsolutelyZariskiLocallyQuasiSeparated

namespace IsScheme

/-- Lemma 68.5.2 (7): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is a scheme
(property (θ)), then `X` is a scheme. -/
@[stacks 03KE]
theorem of_zariskiCover {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X)
    [∀ i, IsScheme (𝒰.X i)] : IsScheme X :=
  sorry

end IsScheme

end AlgebraicGeometry.AlgebraicSpace
