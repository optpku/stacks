/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
import StacksCheckRecall

/-!
# Quasi-coherent algebras on an algebraic space

This file packages quasi-coherent sheaves of `𝒪_X`-algebras on the small étale site of an
algebraic space `X` as the full subcategory of algebras under the commutative structure sheaf
whose restricted unit module is quasi-coherent.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The commutative structure sheaf `𝒪_X` on the small étale site of an algebraic space. -/
abbrev commRingStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  commStructureSheaf X

/-- Forgetting commutativity in `commRingStructureSheaf X` recovers the ring-valued structure
sheaf `𝒪_X`. -/
theorem forget₂_commRingStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (commRingStructureSheaf X) =
      structureSheaf X :=
  rfl

/- The source's quasi-coherent algebra category uses the public canonical structure sheaf. -/
#check (QcAlgebraUnder : ∀ {S : Scheme.{u}}, AlgebraicSpace S → Type _)
#check (QcAlgebraUnder.structureQcAlgebra :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), X.QcAlgebraUnder)
#check (QcAlgebraUnder.isQuasicoherent_restrictedUnit :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder),
    ((restrictionAlong A.obj.hom).obj
      (unitModule (smallEtaleTopology X) (QcAlgebraUnder.sheaf A))).IsQuasicoherent)

end AlgebraicGeometry.AlgebraicSpace
