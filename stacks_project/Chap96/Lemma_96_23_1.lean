/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent.FppfSheaf
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

open AlgebraicGeometry.GroupoidsOver

/- Lemma 96.23.1: a locally quasi-coherent étale module whose canonical comparison
maps are isomorphisms over flat, locally finitely presented scheme morphisms
is a sheaf for the fppf topology. -/
@[stacks 076T] #check
  (AlgebraicGeometry.GroupoidsOver.isSheaf_fppf_of_isLocallyQuasiCoherent :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (F : etaleModules X) [IsLocallyQuasiCoherent F],
      (∀ {x y : X.total} (φ : x ⟶ y),
        Flat (X.p.map φ).left → LocallyOfFinitePresentation (X.p.map φ).left →
          IsIso (moduleComparison φ F)) →
      Presheaf.IsSheaf X.fppfTopology F.val.presheaf)
