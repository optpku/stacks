/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity.Etale
import StacksCheckRecall

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

/- Lemma 77.6.3 (1): the purity assertion in source clause (1). Let `Y` be an
algebraic space over a scheme `S`. Let `g : X' ⟶ X` be an étale morphism of
algebraic spaces over `Y`. Assume the structure morphisms `X' ⟶ Y` and
`X ⟶ Y` are decent and of finite type. Let `ℱ` be a finite type,
quasi-coherent `𝒪_X`-module. Let `y ∈ |Y|`. If `Ass_{X/Y}(ℱ) ⊆ g(|X'|)` and
`g*ℱ` is pure above `y`, then `ℱ` is pure above `y`.
Here `Ass_{X/Y}(ℱ)` is `relativeAssassin f ℱ` with structure map `f : X ⟶ Y`,
`g(|X'|)` is `Set.range (Points.map g)`, `g*ℱ` is `(pullback g).obj ℱ`, and
`X' ⟶ Y` is `g ≫ f`. -/
@[stacks 0CW3]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsPureAlong.of_etale_subset_range :
    ∀ {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [Etale g] [FiniteType f] [Decent f]
    [FiniteType (g ≫ f)] [Decent (g ≫ f)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y)
    (hAss : relativeAssassin f ℱ ⊆ Set.range (Points.map g))
    (hpure : ((pullback g).obj ℱ).IsPureAlong (g ≫ f) y),
    ℱ.IsPureAlong f y)

/- Lemma 77.6.3 (1): the universally-pure assertion in source clause (1). Let
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
#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsUniversallyPureAlong.of_etale_subset_range :
    ∀ {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : X' ⟶ X) [Etale g] [FiniteType f] [Decent f]
    [FiniteType (g ≫ f)] [Decent (g ≫ f)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y)
    (hAss : relativeAssassin f ℱ ⊆ Set.range (Points.map g))
    (hpure : ((pullback g).obj ℱ).IsUniversallyPureAlong (g ≫ f) y),
    ℱ.IsUniversallyPureAlong f y)

/- Lemma 77.6.3 (2): source clause (2). Let `Y` be an algebraic space over a
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
#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.subset_range_of_covers_fiber :
    ∀ {S : Scheme.{u}}
    {Y X X' : AlgebraicSpace S} (f : X ⟶ Y) (g : X' ⟶ X) [Etale g]
    [FiniteType f] [Decent f] [FiniteType (g ≫ f)] [Decent (g ≫ f)]
    [IsAffine Y] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (y : Points Y) (hy : closedPoints (Points Y) = {y})
    (hpure : ℱ.IsPureAlong f y)
    (hF : Points.map f ⁻¹' {y} ⊆ Set.range (Points.map g)),
    relativeAssassin f ℱ ⊆ Set.range (Points.map g))

/- Lemma 77.6.3 (3): source clause (3). Let `Y` be an algebraic space over a
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
#check (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.subset_range_of_covers_inter_fiber :
    ∀ {S : Scheme.{u}}
    {Y X X' : AlgebraicSpace S} (f : X ⟶ Y) (g : X' ⟶ X) [Etale g]
    [FiniteType f] [Decent f] [FiniteType (g ≫ f)] [Decent (g ≫ f)]
    [IsAffine Y] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (y : Points Y) (hy : closedPoints (Points Y) = {y})
    (hpure : ℱ.IsPureAlong f y)
    (hflat : ∀ x : Points X, Points.map f x = y → flatOverAt ℱ f x)
    (hAssF : relativeAssassin f ℱ ∩ Points.map f ⁻¹' {y} ⊆
      Set.range (Points.map g)),
    relativeAssassin f ℱ ⊆ Set.range (Points.map g))

end AlgebraicGeometry.AlgebraicSpace.Modules
