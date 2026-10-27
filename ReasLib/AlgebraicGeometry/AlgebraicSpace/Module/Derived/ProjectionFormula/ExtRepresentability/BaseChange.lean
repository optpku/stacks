/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RelativeExt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.Cohomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent

/-!
# Base change of Ext representations on algebraic spaces

A pseudo-coherent object representing Ext against an ordinary relatively flat tensor
complex remains a representation after cartesian base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape DerivedCategory.TStructure TopologicalSpace
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Pull back a module, place it in degree zero, tensor with `G` as an ordinary
cochain complex, and pass to the derived category. -/
def RepresentsExt.coefficients (f : X ⟶ B) (G : CochainComplex (Modules X) ℤ) :
    Modules B ⥤ ModuleDerived X :=
  Modules.pullback f ⋙ HomologicalComplex.single (Modules X) (up ℤ) 0 ⋙
    tensorLeft G ⋙ DerivedCategory.Q

/-- The Ext boundary for ordinary tensor coefficients is composition with the
connecting morphism of the tensor short exact sequence. -/
def RepresentsExt.targetδ (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (s : ShortComplex (Modules B))
    (hs : (complexTensorPullbackShortComplex f G s).ShortExact) (i : ℤ) :
    Ext⁽i⁾(E, (RepresentsExt.coefficients f G).obj s.X₃) →
      Ext⁽i + 1⁾(E, (RepresentsExt.coefficients f G).obj s.X₁) :=
  fun x ↦ ShiftedHom.comp x (DerivedCategory.triangleOfSES hs).mor₃ (add_comm 1 i)

/-- A derived module represents Ext against ordinary tensor coefficients when additive
Ext equivalences in all integer degrees are natural on quasi-coherent coefficients
and commute with short-exact-sequence boundaries. -/
def RepresentsExt (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B) : Prop :=
  ∃ α : ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
      Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules B) 0).obj F) ≃+
        Ext⁽i⁾(E, (RepresentsExt.coefficients f G).obj F),
    (∀ {F F' : Modules B} (φ : F ⟶ F')
        (hF : quasiCoherentModuleProperty B F) (hF' : quasiCoherentModuleProperty B F')
        (i : ℤ) (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules B) 0).obj F)),
      α F' hF' i (x ≫ ((DerivedCategory.singleFunctor (Modules B) 0).map φ)⟦i⟧') =
        α F hF i x ≫ ((RepresentsExt.coefficients f G).map φ)⟦i⟧') ∧
    (∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
        (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
        (hF₁ : quasiCoherentModuleProperty B s.X₁)
        (hF₂ : quasiCoherentModuleProperty B s.X₂)
        (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
        (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃)),
      α s.X₁ hF₁ (i + 1) (representedExtBoundary L s hs i x) =
        RepresentsExt.targetδ f E G s
          (complexTensorPullback_shortExact f G hG_flat s hs) i (α s.X₃ hF₃ i x))

/-- Additive Ext equivalences that are natural in quasi-coherent coefficients and
compatible with boundaries define an Ext representation. -/
def RepresentsExt.of (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B)
    (α : ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
      Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules B) 0).obj F) ≃+
        Ext⁽i⁾(E, (RepresentsExt.coefficients f G).obj F))
    (hNat : ∀ {F F' : Modules B} (φ : F ⟶ F')
        (hF : quasiCoherentModuleProperty B F) (hF' : quasiCoherentModuleProperty B F')
        (i : ℤ) (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules B) 0).obj F)),
      α F' hF' i (x ≫ ((DerivedCategory.singleFunctor (Modules B) 0).map φ)⟦i⟧') =
        α F hF i x ≫ ((RepresentsExt.coefficients f G).map φ)⟦i⟧')
    (hBoundary : ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
        (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
        (hF₁ : quasiCoherentModuleProperty B s.X₁)
        (hF₂ : quasiCoherentModuleProperty B s.X₂)
        (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
        (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃)),
      α s.X₁ hF₁ (i + 1) (representedExtBoundary L s hs i x) =
        RepresentsExt.targetδ f E G s
          (complexTensorPullback_shortExact f G hG_flat s hs) i (α s.X₃ hF₃ i x)) :
    RepresentsExt f E G L :=
  ⟨α, hNat, hBoundary⟩

/-- Ext representability is equivalent to the full naturality and boundary
compatibility criterion for a family of additive equivalences. -/
theorem RepresentsExt.iff (f : X ⟶ B) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B) :
    RepresentsExt f E G L ↔
  ∃ α : ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
      Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules B) 0).obj F) ≃+
        Ext⁽i⁾(E, (RepresentsExt.coefficients f G).obj F),
    (∀ {F F' : Modules B} (φ : F ⟶ F')
        (hF : quasiCoherentModuleProperty B F) (hF' : quasiCoherentModuleProperty B F')
        (i : ℤ) (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules B) 0).obj F)),
      α F' hF' i (x ≫ ((DerivedCategory.singleFunctor (Modules B) 0).map φ)⟦i⟧') =
        α F hF i x ≫ ((RepresentsExt.coefficients f G).map φ)⟦i⟧') ∧
    (∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
        (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
        (hF₁ : quasiCoherentModuleProperty B s.X₁)
        (hF₂ : quasiCoherentModuleProperty B s.X₂)
        (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
        (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules B) 0).obj s.X₃)),
      α s.X₁ hF₁ (i + 1) (representedExtBoundary L s hs i x) =
        RepresentsExt.targetδ f E G s
          (complexTensorPullback_shortExact f G hG_flat s hs) i (α s.X₃ hF₃ i x)) :=
  sorry

/-- A pseudo-coherent Ext representation remains a representation after cartesian
base change. The represented objects are pulled back in the derived category,
while the coefficient complex is pulled back termwise. -/
theorem RepresentsExt.pullback
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (E : ModuleDerived X)
    (hE_minus : (t.minus : ObjectProperty (ModuleDerived X)) E)
    (hE_coherent :
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X)) E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support :
      ∀ i : ℤ,
        ClosedSubset.ProperOver f
          (Closeds.closure (Modules.moduleSupport (G.X i))))
    (L : ModuleDerived B) (hL : IsPseudoCoherent B L)
    (hrep : RepresentsExt f E G L)
    {X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ B) (sq : IsPullback g' f' f g) :
    RepresentsExt f' ((modulePullbackDerived g').obj E)
      (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G)
      ((modulePullbackDerived g).obj L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
