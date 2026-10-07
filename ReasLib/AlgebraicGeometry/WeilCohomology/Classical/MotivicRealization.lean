module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.CategoryTheory.Monoidal.Functor
public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.ChowMotive.Functor
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical
public import ReasLib.AlgebraicGeometry.WeilCohomology.SmoothProjective
public import ReasLib.CategoryTheory.GradedObject.Instances
public import ReasLib.CategoryTheory.GradedObject.KoszulBraiding

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w y z

namespace WeilCohomology.ClassicalTheory

open AlgebraicGeometry.Correspondence
open GradedObject.Monoidal

/-- A classical Weil cohomology theory over an algebraically closed field with
characteristic-zero coefficients determines a ℚ-linear strong monoidal realization of
Chow motives in graded modules, compatible with the Koszul symmetry and recovering the
theory on every represented smooth projective variety. -/
public theorem existsMotivicRealization
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [CharZero F]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {H : V → Type v} {CH : V → Type y}
    [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
    {Hgrade : ∀ X, ℤ → Submodule F (H X)}
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
    [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle) :
    ∃ (G : ChowMotive k (fun _ ↦ GradedCategory k) ⥤
        GradedObject ℤ (ModuleCat F))
      (monoidal : G.Monoidal)
      (comparison : ∀ X : V,
        ((fun i : ℤ ↦ ModuleCat.of F (Hgrade X i)) :
            GradedObject ℤ (ModuleCat F)) ≅ G.obj (T.geometry.motive X)),
      G.Linear ℚ ∧
        ∀ X Y,
          (@Functor.Monoidal.μIso _ _ _ _ _ _ G monoidal X Y).hom ≫
              G.map (β_ X Y).hom =
            koszulBraidingHom (G.obj X) (G.obj Y) ≫
              (@Functor.Monoidal.μIso _ _ _ _ _ _ G monoidal Y X).hom := sorry

end WeilCohomology.ClassicalTheory
