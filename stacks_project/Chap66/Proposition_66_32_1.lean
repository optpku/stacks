/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AtlasDescent
import StacksCheckRecall

/-!
# Quasi-coherent modules and étale presentations

For an algebraic space `X` over `S` and a surjective étale atlas `φ : U ⟶ X`, quasi-coherent
`𝒪_X`-modules are equivalent to quasi-coherent modules on the associated étale groupoid
`(U, R, s, t, c)`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Proposition 66.32.1: Quasi-coherent modules on an algebraic space are equivalent to
quasi-coherent modules on the kernel-pair groupoid of a surjective étale scheme atlas,
via pullback with its canonical target-to-source action. -/
@[stacks 03M3] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.toGroupoid_isEquivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
      (φ : ofOver U ⟶ X) [Etale φ]
      [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ],
      (QCoh.toGroupoid φ).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.actionIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] (F : QCoh X),
    (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).obj
      ((QCoh.restrictToScheme U).obj ((QCoh.pullback φ).obj F)) ≅
    (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).obj
      ((QCoh.restrictToScheme U).obj ((QCoh.pullback φ).obj F)))

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.toGroupoid_obj :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] (F : QCoh X),
    GroupoidScheme.QCoh.obj ((QCoh.toGroupoid φ).obj F) =
      (QCoh.restrictToScheme U).obj ((QCoh.pullback φ).obj F))

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.toGroupoid_action :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ] (F : QCoh X),
    GroupoidScheme.QCoh.action ((QCoh.toGroupoid φ).obj F) = QCoh.action φ F)
