/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Iteration
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyConnected
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Reduction

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FrobeniusColimit

/-- Pullback along a proper surjective morphism of finite presentation with geometrically
connected fibres is fully faithful on the Frobenius colimits of vector bundles. -/
theorem pullbackFullyFaithful (p : ℕ) [Fact p.Prime]
    {X Y : Scheme.{u}} [Y.IsCharP p] [X.IsCharP p]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Surjective f] [Scheme.Hom.FinitePresentation f]
    (hconnected : ∀ y : Y, GeometricallyConnected (f.fiberToSpecResidueField y))
    (G : vectorBundleColimit p Y ⥤ vectorBundleColimit p X)
    [IsStagewisePullback p f G] :
    Nonempty G.FullyFaithful := sorry

/-- A finite locally free module whose restriction to every reduced fibre becomes finite free
after a fibre-dependent Frobenius pullback descends after one global Frobenius pullback. -/
theorem eventuallyDescends (p : ℕ) [Fact p.Prime]
    {X Y : Scheme.{u}} [Y.IsCharP p]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Surjective f] [Scheme.Hom.FinitePresentation f]
    (hconnected : ∀ y : Y, GeometricallyConnected (f.fiberToSpecResidueField y))
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (hfree : ∀ y : Y, ∃ n_y r_y : ℕ,
      Nonempty
        ((Scheme.Modules.pullback
          (Scheme.reductionι (f.fiber y) ≫ f.fiberι y ≫
            @Scheme.Hom.absoluteFrobeniusPowSource p _ X Y f _ n_y)).obj E ≅
          SheafOfModules.freeFin r_y)) :
    ∃ n : ℕ, ∃ F : Y.Modules, ∃ _ : F.IsFiniteLocallyFree,
      Nonempty
        ((Scheme.Modules.pullback
          (@Scheme.Hom.absoluteFrobeniusPowSource p _ X Y f _ n)).obj E ≅
          (Scheme.Modules.pullback f).obj F) := sorry

/-- An explicit eventual descent isomorphism puts the stage-zero bundle in the essential image
of a stagewise pullback functor. -/
theorem stage_mem_essImage_of_descends (p : ℕ) [Fact p.Prime]
    {X Y : Scheme.{u}} [Y.IsCharP p] [X.IsCharP p]
    (f : X ⟶ Y)
    (G : vectorBundleColimit p Y ⥤ vectorBundleColimit p X)
    [IsStagewisePullback p f G] (E : vectorBundles X)
    (hdesc : ∃ n : ℕ, ∃ F : Y.Modules, ∃ _ : F.IsFiniteLocallyFree,
      Nonempty
        ((Scheme.Modules.pullback
          (@Scheme.Hom.absoluteFrobeniusPowSource p _ X Y f _ n)).obj (ULift.down E).obj ≅
          (Scheme.Modules.pullback f).obj F)) :
    G.essImage ((stage p X 0).obj E) := sorry

end AlgebraicGeometry.Scheme.FrobeniusColimit
