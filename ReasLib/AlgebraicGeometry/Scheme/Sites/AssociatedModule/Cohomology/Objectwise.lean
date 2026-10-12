/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise

/-!
# Objectwise cohomology of associated modules

This module compares scheme cohomology after pullback with objectwise cohomology
of the associated module on a standard site.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- Scheme cohomology after pullback to an object of a standard big site agrees with
objectwise cohomology of the associated module on that site. -/
theorem cohomologyAtObject_isomorphic_big
    (τ : StandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : Over S) (p : ℕ)
    [HasSheafify (τ.overTopology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (τ.overTopology S) AddCommGrpCat.{u})] :
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(U.left, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology ((Scheme.Modules.pullback U.hom).obj F) p))
      ((Sheaf.cohomologyAtObjectFunctor (τ.overTopology S) U p).obj
        ((SheafOfModules.toSheaf (bigStructureSheaf τ S)).obj (big τ S F))) := sorry

/-- Scheme cohomology after pullback to an object of a selected small site agrees with
objectwise cohomology of the associated module on that site. -/
theorem cohomologyAtObject_isomorphic_small
    (σ : SmallStandardTopology) (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : σ.site S) (p : ℕ)
    [HasSheafify (σ.topology S) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (σ.topology S) AddCommGrpCat.{u})] :
    IsIsomorphic
      ((forget₂ (ModuleCat Γ(((σ.toOver S).obj U).left, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology
          ((Scheme.Modules.pullback ((σ.toOver S).obj U).hom).obj F) p))
      ((Sheaf.cohomologyAtObjectFunctor (σ.topology S) U p).obj
        ((SheafOfModules.toSheaf (smallStructureSheaf σ S)).obj (small σ S F))) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
