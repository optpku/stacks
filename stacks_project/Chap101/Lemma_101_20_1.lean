/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_7_1_Product
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation
public import stacks_project.Chap101.Definition_101_4_2_Separation

/-!
# Separation properties of a quotient stack from its presentation

For a groupoid in algebraic spaces with flat, locally finitely presented
source and target, separatedness of `R ⟶ U × U` or of `U` and `R` implies
that the object diagonal of `[U/R]` is separated, while local quasi-finiteness
or properness of that presentation yields that `[U/R]` is quasi-DM or
separated over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry GroupoidAlgebraicSpace Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 101.20.1 (1): let `(U, R, s, t, c)` be a groupoid in algebraic spaces
such that `s, t : R ⟶ U` are flat and locally of finite presentation. Let
`X = [U/R]` be the associated algebraic stack. If `R ⟶ U × U` is separated,
then `Δ_X` is separated. Formalized for a groupoid `G` in algebraic spaces
over an algebraic space `B` over `S`, with `[U/R]` as `G.quotientStack`,
`R ⟶ U × U` as `prod.lift G.t.left G.s.left`, and `Δ_X` as
`FiberedCategoryOver.Groupoids.diagonal G.quotientStack`. -/
@[stacks 0DTY]
theorem has_separated_diagonal {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack G.quotientStack]
    [AlgebraicSpace.Separated (prod.lift G.t.left G.s.left)] :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
      (diagonal.{u + 1, u, u + 1} G.quotientStack) :=
  sorry

/-- Lemma 101.20.1 (2): let `(U, R, s, t, c)` be a groupoid in algebraic spaces
such that `s, t : R ⟶ U` are flat and locally of finite presentation. Let
`X = [U/R]` be the associated algebraic stack. If `U` and `R` are separated,
then `Δ_X` is separated. -/
@[stacks 0DTY]
theorem has_separated_diagonal_of_isSeparated {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack G.quotientStack] [AlgebraicSpace.IsSeparated G.U.left]
    [AlgebraicSpace.IsSeparated G.R.left] :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
      (diagonal.{u + 1, u, u + 1} G.quotientStack) :=
  sorry

/-- Lemma 101.20.1 (3): let `(U, R, s, t, c)` be a groupoid in algebraic spaces
such that `s, t : R ⟶ U` are flat and locally of finite presentation. Let
`X = [U/R]` be the associated algebraic stack. If `R ⟶ U × U` is locally
quasi-finite, then `X` is quasi-DM. -/
@[stacks 0DTY, instance]
instance instIsQuasiDMOver_of_locallyQuasiFinite_j {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack G.quotientStack]
    [AlgebraicSpace.LocallyQuasiFinite (prod.lift G.t.left G.s.left)] :
    AlgebraicStack.IsQuasiDMOver G.quotientStack :=
  sorry

/-- Lemma 101.20.1 (4): let `(U, R, s, t, c)` be a groupoid in algebraic spaces
such that `s, t : R ⟶ U` are flat and locally of finite presentation. Let
`X = [U/R]` be the associated algebraic stack. If `s, t : R ⟶ U` are locally
quasi-finite, then `X` is quasi-DM. -/
@[stacks 0DTY, instance]
instance instIsQuasiDMOver_of_locallyQuasiFinite {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack G.quotientStack]
    [AlgebraicSpace.LocallyQuasiFinite G.s.left]
    [AlgebraicSpace.LocallyQuasiFinite G.t.left] :
    AlgebraicStack.IsQuasiDMOver G.quotientStack :=
  sorry

/-- Lemma 101.20.1 (5): let `(U, R, s, t, c)` be a groupoid in algebraic spaces
such that `s, t : R ⟶ U` are flat and locally of finite presentation. Let
`X = [U/R]` be the associated algebraic stack. If `R ⟶ U × U` is proper, then
`X` is separated. -/
@[stacks 0DTY, instance]
instance instIsSeparatedOver_of_proper_j {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack G.quotientStack]
    [AlgebraicSpace.Proper (prod.lift G.t.left G.s.left)] :
    AlgebraicStack.IsSeparatedOver G.quotientStack :=
  sorry

/-- Lemma 101.20.1 (6): let `(U, R, s, t, c)` be a groupoid in algebraic spaces
such that `s, t : R ⟶ U` are flat and locally of finite presentation. Let
`X = [U/R]` be the associated algebraic stack. If `s, t : R ⟶ U` are proper
and `U` is separated, then `X` is separated. -/
@[stacks 0DTY, instance]
instance instIsSeparatedOver_of_proper {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G]
    [AlgebraicStack G.quotientStack] [AlgebraicSpace.Proper G.s.left]
    [AlgebraicSpace.Proper G.t.left] [AlgebraicSpace.IsSeparated G.U.left] :
    AlgebraicStack.IsSeparatedOver G.quotientStack :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
