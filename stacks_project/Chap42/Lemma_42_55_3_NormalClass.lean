/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.NormalSheaf
public import ReasLib.AlgebraicGeometry.LocalizedChern.RegularImmersion

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

noncomputable section

universe u

/- The normal-sheaf bivariant class through its canonical mathematical owner. -/
#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.normalClass :
    ∀ {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (p : X ⟶ S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [LocallyOfFiniteType (i ≫ p)] [IsClosedImmersion i]
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf i)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i) ≅ Scheme.Hom.conormalSheaf i)
    (D : ClosedDeformation (i ≫ p) p i rfl (ofNormalSheaf i r e)),
    BivariantClass delta (overHom (i ≫ p) p i rfl) (r : ℤ))
