/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/- Lemma 63.7.1: Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. Let `Λ` be a ring. The functors `f_!` and `f^!` of
Definition 63.4.4 and Lemma 63.6.1 induce adjoint functors
`f_! = lowerShriekModuleDerived : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` and
`Rf^! = upperShriekModuleDerived : D(Y_étale, Λ) ⥤ D(X_étale, Λ)`
on derived categories. Stacks locally quasi-finite is rendered as
`[LocallyQuasiFinite f]` together with `[LocallyOfFiniteType f]`, as in
`lowerShriek_exact`. -/
@[stacks 0F5N]
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekModuleDerivedAdjunction f Λ :
  AlgebraicGeometry.Scheme.Etale.lowerShriekModuleDerived f Λ ⊣
    AlgebraicGeometry.Scheme.Etale.upperShriekModuleDerived f Λ)

end
