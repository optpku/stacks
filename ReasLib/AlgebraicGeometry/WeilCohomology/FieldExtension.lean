/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.GradedPullback
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w x y z

namespace WeilCohomology.SchemePreWeilTheory

/-- The spectrum morphism between explicit representatives in a tower of field extensions. -/
noncomputable def representedSpecMap
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0} {H Picard : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {k' k'' : Type u} [Field k'] [Field k''] [Algebra k k'] [Algebra k' k'']
    [Algebra k k''] [IsScalarTower k k' k''] {X' X'' : V}
    (e' : T.scheme.obj X' ≅ Over.mk (FieldExtension.specMap k k'))
    (e'' : T.scheme.obj X'' ≅ Over.mk (FieldExtension.specMap k k'')) : X'' ⟶ X' :=
  T.scheme_fullyFaithful.preimage
    (e''.hom ≫ (Over.homMk (FieldExtension.specMap k' k'')
      (Scheme.AffineBaseChange.specMap_comp k k' k'') :
        (Over.mk (FieldExtension.specMap k k'') : SchemeOverField k) ⟶
          (Over.mk (FieldExtension.specMap k k') : SchemeOverField k)) ≫ e'.inv)

/-- The realization of `representedSpecMap` is the conjugated canonical spectrum map. -/
theorem scheme_representedSpecMap
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0} {H Picard : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
    {k' k'' : Type u} [Field k'] [Field k''] [Algebra k k'] [Algebra k' k'']
    [Algebra k k''] [IsScalarTower k k' k''] {X' X'' : V}
    (e' : T.scheme.obj X' ≅ Over.mk (FieldExtension.specMap k k'))
    (e'' : T.scheme.obj X'' ≅ Over.mk (FieldExtension.specMap k k'')) :
    T.scheme.map (T.representedSpecMap e' e'') =
      e''.hom ≫ (Over.homMk (FieldExtension.specMap k' k'')
        (Scheme.AffineBaseChange.specMap_comp k k' k'') :
          (Over.mk (FieldExtension.specMap k k'') : SchemeOverField k) ⟶
            (Over.mk (FieldExtension.specMap k k') : SchemeOverField k)) ≫ e'.inv := sorry

/-- Degree-zero pullback along a compatible finite-separable field tower is injective. -/
theorem degreeZeroPullback_injective_of_finiteSeparable
    {k k' k'' : Type u} [Field k] [Field k'] [Field k'']
    [Algebra k k'] [Algebra k' k''] [Algebra k k''] [IsScalarTower k k' k'']
    [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    [FiniteDimensional k' k''] [Algebra.IsSeparable k' k'']
    {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0} {H Picard : V → Type x}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]
    (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard) {X' X'' : V}
    (e' : T.scheme.obj X' ≅ Over.mk (FieldExtension.specMap k k'))
    (e'' : T.scheme.obj X'' ≅ Over.mk (FieldExtension.specMap k k'')) :
    Function.Injective (T.pullbackGrade (T.representedSpecMap e' e'') (0, 0)) := sorry

end WeilCohomology.SchemePreWeilTheory
