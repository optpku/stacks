/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Differentials
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.Etale.Small
open Scheme.Etale.Small
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/- Lemma 76.7.1: the associated étale sheaf of scheme differentials is
canonically isomorphic to the small-étale site differentials, compatibly with
universal derivations. -/
@[stacks 04CS]
#check (AlgebraicGeometry.Scheme.Etale.Small.existsUnique_associatedModuleIso f :
  ∃! e : RingedSite.Hom.relativeDifferentials.{u + 1, u} (commRingedHom f) ≅
    StandardSmall.comm .etale X (Ω[f.toShHom]),
    ∀ (U : X.Etaleᵒᵖ)
      (t : (StandardSmall.commStructureSheaf .etale X).obj.obj U),
      etaleComparisonSections f U.unop
        (ULift.down (e.hom.val.app U
          ((RingedSite.Hom.relativeDifferential (commRingedHom f)).d t))) =
        (d[(U.unop.hom ≫ f).toShHom]).d (ULift.down t))
