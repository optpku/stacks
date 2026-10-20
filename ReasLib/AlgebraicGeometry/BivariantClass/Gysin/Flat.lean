/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Factorization
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback.DimensionLocus

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle Gysin

/-- For a flat local complete intersection morphism with an immersion–smooth
factorization, the immersion is regular and admits a normal-sheaf deformation
realization whose Gysin coefficients equal flat pullback in every integer degree. -/
theorem gysin_eq_flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [Flat f.left] {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (g : P ⟶ Y) [IsImmersion i.left] [hg : Smooth g.left]
    (hfac : i ≫ g = f) :
    ∃ hreg : IsRegularImmersion i.left,
    ∃ e : Scheme.Modules.dual (normalSheaf i.left) ≅ conormalSheaf i.left,
    ∃ D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (@normalBundle X.left P.left i.left hreg e).toCoborder,
      (fun p : ℤ ↦ @factorizationClassDegree S inferInstance δ inferInstance X Y P
        inferInstance inferInstance inferInstance f i g hreg hg hfac e D p) =
        (fun p : ℤ ↦ flatPullbackDegree δ f p) := sorry

end AlgebraicGeometry.BivariantClass
