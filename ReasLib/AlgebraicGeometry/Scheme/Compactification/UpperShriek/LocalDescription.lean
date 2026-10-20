/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.PlusModel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine.BoundedBelow
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- On compatible affine opens of a finite-type separated morphism, affine derived global
sections identify the restriction of upper shriek with the module upper-shriek functor
associated to a chosen polynomial presentation of the induced ring homomorphism. -/
theorem upperShriekAffineRestrictionIsomorphic
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (C : Of Y.obj.left (Over.mk f.hom.left))
    (M : DerivedQCoh.PlusRightAdjoint C.obj.right.hom)
    (U : affineOpens X.obj.left) (V : affineOpens Y.obj.left)
    (hUV : U ≤ f.hom.left ⁻¹ᵁ V)
    (p : ModuleCat.UpperShriek.Presentation
      (CommRingCat.Hom.hom (Hom.appLE f.hom.left V U hUV)))
    (E : DerivedQCoh.Plus Y.obj.left) :
    IsIsomorphic
      ((upperShriek f C M.plus ⋙
        DerivedQCoh.OpenImmersion.pullbackPlus U.2.fromSpec ⋙
        DerivedQCoh.affineGlobalSectionsPlus Γ(X.obj.left, U) ⋙
        DerivedCategory.Plus.ι).obj E)
      (p.functor.obj
        ((DerivedQCoh.OpenImmersion.pullbackPlus V.2.fromSpec ⋙
          DerivedQCoh.affineGlobalSectionsPlus Γ(Y.obj.left, V) ⋙
          DerivedCategory.Plus.ι).obj E)) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of
