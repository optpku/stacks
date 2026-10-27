/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.InternalHom.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Pullback.EtaleRestriction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.InternalHom.FinitePresentation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Pullback

/-! # Flat pullback of quasi-coherent internal Hom -/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y]

/-- Pullback compares with internal Hom in locally quasi-coherent étale
modules with flat base change, using the canonical topology-restriction isomorphism. -/
def moduleSheafHomLQCohFbc_pullback (f : X ⟶ Y) (F : fppfModules Y) (G : QCoh Y)
    [F.IsFinitePresentation] :
    (LQCohFbc.inverseImage f).obj (moduleSheafHomLQCohFbc F G) ⟶
      moduleSheafHomLQCohFbc ((modulePullback f).obj F) ((QCoh.pullback f).obj G) :=
  homMk
    (moduleSheafHomOnEtale_pullback f ((restriction Y).obj F)
        ((restriction Y).obj G.obj) ≫
      (moduleSheafHomOnEtale_homEquiv
        ((restriction X).obj ((modulePullback f).obj F))
        ((restriction X).obj ((QCoh.pullback f).obj G).obj)
        (moduleSheafHomEtale
          ((etaleModuleInverseImage f).obj ((restriction Y).obj F))
          ((etaleModuleInverseImage f).obj ((restriction Y).obj G.obj)))).symm
        (moduleTensorMap.{u + 1, u, u} (𝟙 _) ((modulePullbackRestrictionIso f).hom.app F) ≫
          moduleSheafHomOnEtale_homEquiv
            ((etaleModuleInverseImage f).obj ((restriction Y).obj F))
            ((etaleModuleInverseImage f).obj ((restriction Y).obj G.obj))
            (moduleSheafHomEtale
              ((etaleModuleInverseImage f).obj ((restriction Y).obj F))
              ((etaleModuleInverseImage f).obj ((restriction Y).obj G.obj))) (𝟙 _) ≫
          (modulePullbackRestrictionIso f).inv.app G.obj))

namespace QCoh

/-- The comparison from pullback of quasi-coherent internal Hom to internal
Hom of pullbacks is coreflector comparison followed by the étale Hom comparison. -/
def internalHomFP_pullback (f : X ⟶ Y)
    (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation] :
    (pullback f).obj (internalHomFP F G) ⟶
      internalHomFP ((modulePullback f).obj F) ((pullback f).obj G) :=
  (LQCohFbc.toQCoh_pullback f).app (moduleSheafHomLQCohFbc F G) ≫
    (LQCohFbc.toQCoh X).map (moduleSheafHomLQCohFbc_pullback f F G)

/-- Flat pullback makes the canonical quasi-coherent internal-Hom comparison invertible. -/
instance internalHomFP_pullback_isIso (f : X ⟶ Y) [AlgebraicStack.Flat f]
    (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation] :
    IsIso (internalHomFP_pullback f F G) := sorry

/-- Pullback along a flat morphism of algebraic stacks commutes canonically
with quasi-coherent internal Hom from a finitely presented module. -/
def internalHomFP_pullbackIso (f : X ⟶ Y) [AlgebraicStack.Flat f]
    (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation] :
    (pullback f).obj (internalHomFP F G) ≅
      internalHomFP ((modulePullback f).obj F) ((pullback f).obj G) :=
  asIso (internalHomFP_pullback f F G)

/-- The forward map of the flat-pullback internal-Hom isomorphism is the canonical comparison. -/
theorem internalHomFP_pullbackIso_hom (f : X ⟶ Y) [AlgebraicStack.Flat f]
    (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation] :
    (internalHomFP_pullbackIso f F G).hom = internalHomFP_pullback f F G :=
  rfl

end QCoh

end AlgebraicGeometry.GroupoidsOver
