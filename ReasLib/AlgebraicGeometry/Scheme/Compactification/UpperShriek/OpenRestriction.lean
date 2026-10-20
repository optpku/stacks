/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.OpenImmersion

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- For a commutative square of finite-type separated schemes whose horizontal maps are
open immersions, upper shriek commutes with restriction to the open subschemes. -/
theorem upperShriek_openRestriction_isomorphic
    {S : Scheme.{u}} [IsNoetherian S]
    {U X V Y : FiniteTypeSeparatedOver S}
    (j : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (j' : V ⟶ Y)
    (h_comm : j ≫ f = g ≫ j')
    [IsOpenImmersion j.hom.left] [IsOpenImmersion j'.hom.left]
    (P_f : Of Y.obj.left (Over.mk f.hom.left))
    (A_f : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_f))
    (P_g : Of V.obj.left (Over.mk g.hom.left))
    (A_g : DerivedQCoh.PlusRightAdjoint (ambientMorphism P_g)) :
    IsIsomorphic
      (upperShriek f P_f A_f.plus ⋙
        DerivedQCoh.OpenImmersion.pullbackPlus j.hom.left)
      (DerivedQCoh.OpenImmersion.pullbackPlus j'.hom.left ⋙
        upperShriek g P_g A_g.plus) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of
