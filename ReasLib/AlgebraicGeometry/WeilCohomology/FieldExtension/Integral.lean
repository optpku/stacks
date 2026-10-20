module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w x y z

namespace WeilCohomology.SchemePreWeilTheory

/-- A presentation object isomorphic to the spectrum of a field extension is
nonempty equidimensional of dimension zero. -/
theorem fieldSpectrum_isNonemptyEquidimensional
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
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
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} (eX : T.scheme.obj X ≅ Over.mk (FieldExtension.specMap k k')) :
    T.IsNonemptyEquidimensional X 0 := sorry

/-- For a finite Galois extension, the integral of one on a represented field
spectrum equals the extension degree in the coefficient field. -/
theorem integral_one_eq_finrank_of_galois
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k']
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
      cyclePullback cyclePushforward pointCycle H Picard)
    {X : V} (eX : T.scheme.obj X ≅ Over.mk (FieldExtension.specMap k k')) :
    T.integral (T.fieldSpectrum_isNonemptyEquidimensional eX) 1 =
      (Module.finrank k k' : F) := sorry

end WeilCohomology.SchemePreWeilTheory
