/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Colimits
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.InternalHom
public import stacks_project.Chap96.Lemma_96_12_5_AssociatedModules

/-!
# Topology comparison of quasi-coherent modules

Compatibility checks for the canonical topology transports, tensor comparison,
and internal-Hom comparison determined by a common evaluation.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite

universe u

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toAssociatedModules :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology),
    QCoh X ⥤ associatedModules X τ)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toEtaleModules :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), QCoh X ⥤ etaleModules X)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.toLQCoh :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), QCoh X ⥤ LQCoh X)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.tensorComparison :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (τ : StandardTopology) (F G : QCoh X),
    moduleTensorAssociated ((QCoh.toCommAssociatedModules X τ).obj F)
      ((QCoh.toCommAssociatedModules X τ).obj G) ⟶
        (QCoh.toCommAssociatedModules X τ).obj (QCoh.quasicoherentTensor F G))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.internalHomComparison :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (τ : StandardTopology)
    (F G H : QCoh X) (ev : QCoh.quasicoherentTensor F H ⟶ G),
    (commAssociatedModulesLiftFunctor X τ).obj ((QCoh.toCommAssociatedModules X τ).obj H) ⟶
      QCoh.associatedInternalHomLift
        ((QCoh.toCommAssociatedModules X τ).obj F)
        ((QCoh.toCommAssociatedModules X τ).obj G))
