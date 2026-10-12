/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap77.Lemma_77_3_2_Purity
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Lemma 77.6.3

Purity and relative associated points along an étale morphism of algebraic
spaces: purity transfers from an étale cover of the assassin, and conversely
the assassin is covered in the affine-local case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace IsPureAlong

/-- Lemma 77.6.3 (1): the purity assertion in source clause (1). Let `Y` be an
algebraic space over a scheme `S`. Let `g : X' ⟶ X` be an étale morphism of
algebraic spaces over `Y`. Assume the structure morphisms `X' ⟶ Y` and
`X ⟶ Y` are decent and of finite type. Let `ℱ` be a finite type,
quasi-coherent `𝒪_X`-module. Let `y ∈ |Y|`. If `Ass_{X/Y}(ℱ) ⊆ g(|X'|)` and
`g*ℱ` is pure above `y`, then `ℱ` is pure above `y`.
Here `Ass_{X/Y}(ℱ)` is `relativeAssassin f ℱ` with structure map `f : X ⟶ Y`,
`g(|X'|)` is `Set.range (Points.map g)`, `g*ℱ` is `(pullback g).obj ℱ`, and
`X' ⟶ Y` is `g ≫ f`. -/
@[stacks 0CW3]
theorem of_etale_subset_range {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [Etale g] [FiniteType f] [Decent f]
    [FiniteType (g ≫ f)] [Decent (g ≫ f)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y)
    (hAss : relativeAssassin f ℱ ⊆ Set.range (Points.map g))
    (hpure : ((pullback g).obj ℱ).IsPureAlong (g ≫ f) y) :
    ℱ.IsPureAlong f y :=
  sorry

end IsPureAlong

namespace IsUniversallyPureAlong

/-- Lemma 77.6.3 (2): the universally-pure assertion in source clause (1). Let
`Y` be an algebraic space over a scheme `S`. Let `g : X' ⟶ X` be an étale
morphism of algebraic spaces over `Y`. Assume the structure morphisms
`X' ⟶ Y` and `X ⟶ Y` are decent and of finite type. Let `ℱ` be a finite
type, quasi-coherent `𝒪_X`-module. Let `y ∈ |Y|`. If `Ass_{X/Y}(ℱ) ⊆ g(|X'|)`
and `g*ℱ` is universally pure above `y`, then `ℱ` is universally pure
above `y`.
Here `Ass_{X/Y}(ℱ)` is `relativeAssassin f ℱ` with structure map `f : X ⟶ Y`,
`g(|X'|)` is `Set.range (Points.map g)`, `g*ℱ` is `(pullback g).obj ℱ`, and
`X' ⟶ Y` is `g ≫ f`. -/
@[stacks 0CW3]
theorem of_etale_subset_range {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [Etale g] [FiniteType f] [Decent f]
    [FiniteType (g ≫ f)] [Decent (g ≫ f)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y)
    (hAss : relativeAssassin f ℱ ⊆ Set.range (Points.map g))
    (hpure : ((pullback g).obj ℱ).IsUniversallyPureAlong (g ≫ f) y) :
    ℱ.IsUniversallyPureAlong f y :=
  sorry

end IsUniversallyPureAlong

namespace relativeAssassin

/-- Lemma 77.6.3 (3): source clause (2). Let `Y` be an algebraic space over a
scheme `S`. Let `g : X' ⟶ X` be an étale morphism of algebraic spaces over
`Y`. Assume the structure morphisms `X' ⟶ Y` and `X ⟶ Y` are decent and of
finite type. Let `ℱ` be a finite type, quasi-coherent `𝒪_X`-module. Let
`y ∈ |Y|`, and write `F = f⁻¹({y}) ⊂ |X|`. If `ℱ` is pure above `y`,
`g(|X'|)` contains `F`, and `Y` is affine local with closed point `y`, then
`Ass_{X/Y}(ℱ) ⊆ g(|X'|)`.
Here `F` is `Points.map f ⁻¹' {y}`, `g(|X'|)` is `Set.range (Points.map g)`,
`Ass_{X/Y}(ℱ)` is `relativeAssassin f ℱ`, affine-local means `IsAffine Y`
with `closedPoints (Points Y) = {y}`, and `X' ⟶ Y` is `g ≫ f`. -/
@[stacks 0CW3]
theorem subset_range_of_covers_fiber {S : Scheme.{u}}
    {Y X X' : AlgebraicSpace S} (f : X ⟶ Y) (g : X' ⟶ X) [Etale g]
    [FiniteType f] [Decent f] [FiniteType (g ≫ f)] [Decent (g ≫ f)]
    [IsAffine Y] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (y : Points Y) (hy : closedPoints (Points Y) = {y})
    (hpure : ℱ.IsPureAlong f y)
    (hF : Points.map f ⁻¹' {y} ⊆ Set.range (Points.map g)) :
    relativeAssassin f ℱ ⊆ Set.range (Points.map g) :=
  sorry

/-- Lemma 77.6.3 (4): source clause (3). Let `Y` be an algebraic space over a
scheme `S`. Let `g : X' ⟶ X` be an étale morphism of algebraic spaces over
`Y`. Assume the structure morphisms `X' ⟶ Y` and `X ⟶ Y` are decent and of
finite type. Let `ℱ` be a finite type, quasi-coherent `𝒪_X`-module. Let
`y ∈ |Y|`, and write `F = f⁻¹({y}) ⊂ |X|`. If `ℱ` is pure above `y`, `ℱ` is
flat at all points of `F`, `g(|X'|)` contains `Ass_{X/Y}(ℱ) ∩ F`, and `Y` is
affine local with closed point `y`, then `Ass_{X/Y}(ℱ) ⊆ g(|X'|)`.
Here `F` is `Points.map f ⁻¹' {y}`, `g(|X'|)` is `Set.range (Points.map g)`,
`Ass_{X/Y}(ℱ)` is `relativeAssassin f ℱ`, flatness at points of `F` is
`flatOverAt ℱ f`, affine-local means `IsAffine Y` with
`closedPoints (Points Y) = {y}`, and `X' ⟶ Y` is `g ≫ f`. -/
@[stacks 0CW3]
theorem subset_range_of_covers_inter_fiber {S : Scheme.{u}}
    {Y X X' : AlgebraicSpace S} (f : X ⟶ Y) (g : X' ⟶ X) [Etale g]
    [FiniteType f] [Decent f] [FiniteType (g ≫ f)] [Decent (g ≫ f)]
    [IsAffine Y] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (y : Points Y) (hy : closedPoints (Points Y) = {y})
    (hpure : ℱ.IsPureAlong f y)
    (hflat : ∀ x : Points X, Points.map f x = y → flatOverAt ℱ f x)
    (hAssF : relativeAssassin f ℱ ∩ Points.map f ⁻¹' {y} ⊆
      Set.range (Points.map g)) :
    relativeAssassin f ℱ ⊆ Set.range (Points.map g) :=
  sorry

/-- A relatively associated point of `ℱ` over `Y` lies in `g(|X'|)` as soon as
`ℱ` is pure above the unique closed point of affine-local `Y` and the fibre
`f⁻¹({y})` is contained in the image of `|X'|`. -/
theorem mem_range_of_covers_fiber {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [Etale g] [FiniteType f] [Decent f]
    [FiniteType (g ≫ f)] [Decent (g ≫ f)] [IsAffine Y] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y)
    (hy : closedPoints (Points Y) = {y}) (hpure : ℱ.IsPureAlong f y)
    (hF : Points.map f ⁻¹' {y} ⊆ Set.range (Points.map g)) {x : Points X}
    (hx : x ∈ relativeAssassin f ℱ) :
    x ∈ Set.range (Points.map g) :=
  sorry

/-- A relatively associated point of `ℱ` over `Y` lies in `g(|X'|)` as soon as
`ℱ` is pure above the unique closed point of affine-local `Y`, `ℱ` is flat
along the fibre `f⁻¹({y})`, and that fibre meets the assassin only in the
image of `|X'|`. -/
theorem mem_range_of_covers_inter_fiber {S : Scheme.{u}}
    {Y X X' : AlgebraicSpace S} (f : X ⟶ Y) (g : X' ⟶ X) [Etale g]
    [FiniteType f] [Decent f] [FiniteType (g ≫ f)] [Decent (g ≫ f)]
    [IsAffine Y] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (y : Points Y) (hy : closedPoints (Points Y) = {y})
    (hpure : ℱ.IsPureAlong f y)
    (hflat : ∀ x : Points X, Points.map f x = y → flatOverAt ℱ f x)
    (hAssF : relativeAssassin f ℱ ∩ Points.map f ⁻¹' {y} ⊆
      Set.range (Points.map g)) {x : Points X}
    (hx : x ∈ relativeAssassin f ℱ) :
    x ∈ Set.range (Points.map g) :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
