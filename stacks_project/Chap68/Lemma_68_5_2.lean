module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiLocalConditions

/-!
# Zariski locality of conditions on algebraic spaces

If `P` is one of the properties (α), (β), (γ), (δ), (ε), (ζ), or (θ) of
algebraic spaces from Lemma 68.5.1, and `X = ⋃ 𝒰.X i` is a Zariski open
covering with each `𝒰.X i` satisfying `P`, then `X` satisfies `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

/- Lemma 68.5.2 (1): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` has property (α),
then `X` has property (α). -/
@[stacks 03KE] #check
  (AlgebraicGeometry.AlgebraicSpace.HasPropertyAlpha.of_zariskiCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (𝒰 : AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, v} X),
      [∀ i, AlgebraicGeometry.AlgebraicSpace.HasPropertyAlpha (𝒰.X i)] →
        AlgebraicGeometry.AlgebraicSpace.HasPropertyAlpha X)

/- Lemma 68.5.2 (2): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` has property (β),
then `X` has property (β). -/
@[stacks 03KE] #check
  (AlgebraicGeometry.AlgebraicSpace.HasPropertyBeta.of_zariskiCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (𝒰 : AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, v} X),
      [∀ i, AlgebraicGeometry.AlgebraicSpace.HasPropertyBeta (𝒰.X i)] →
        AlgebraicGeometry.AlgebraicSpace.HasPropertyBeta X)

/- Lemma 68.5.2 (3): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is decent
(property (γ)), then `X` is decent. -/
@[stacks 03KE] #check
  (AlgebraicGeometry.AlgebraicSpace.IsDecent.of_zariskiCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (𝒰 : AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, v} X),
      [∀ i, AlgebraicGeometry.AlgebraicSpace.IsDecent (𝒰.X i)] →
        AlgebraicGeometry.AlgebraicSpace.IsDecent X)

/- Lemma 68.5.2 (4): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is reasonable
(property (δ)), then `X` is reasonable. -/
@[stacks 03KE] #check
  (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_zariskiCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (𝒰 : AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, v} X),
      [∀ i, AlgebraicGeometry.AlgebraicSpace.IsReasonable (𝒰.X i)] →
        AlgebraicGeometry.AlgebraicSpace.IsReasonable X)

/- Lemma 68.5.2 (5): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is very reasonable
(property (ε)), then `X` is very reasonable. -/
@[stacks 03KE] #check
  (AlgebraicGeometry.AlgebraicSpace.IsVeryReasonable.of_zariskiCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (𝒰 : AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, v} X),
      [∀ i, AlgebraicGeometry.AlgebraicSpace.IsVeryReasonable (𝒰.X i)] →
        AlgebraicGeometry.AlgebraicSpace.IsVeryReasonable X)

/- Lemma 68.5.2 (6): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is absolutely
Zariski locally quasi-separated (property (ζ)), then `X` is absolutely
Zariski locally quasi-separated. -/
@[stacks 03KE] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyZariskiLocallyQuasiSeparated.of_zariskiCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (𝒰 : AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, v} X),
      [∀ i,
        AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyZariskiLocallyQuasiSeparated (𝒰.X i)] →
        AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyZariskiLocallyQuasiSeparated X)

/- Lemma 68.5.2 (7): let `S` be a scheme and `X` an algebraic space over `S`.
If `X = ⋃ 𝒰.X i` is a Zariski open covering and each `𝒰.X i` is a scheme
(property (θ)), then `X` is a scheme. -/
@[stacks 03KE] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_zariskiCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (𝒰 : AlgebraicGeometry.AlgebraicSpace.ZariskiCover.{u, v} X),
      [∀ i, AlgebraicGeometry.AlgebraicSpace.IsScheme (𝒰.X i)] →
        AlgebraicGeometry.AlgebraicSpace.IsScheme X)
