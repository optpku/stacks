/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite.Torsion
import StacksCheckRecall

/-!
# Torsion cohomology sheaves under derived compact-support direct image

For a locally quasi-finite morphism, exact `f_!` preserves complexes with
torsion cohomology sheaves, by the stalk formula of Lemma 63.4.5.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section Sheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
  [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

#check (AlgebraicGeometry.Scheme.Etale.lowerShriek_isLocallyTorsion f :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    IsLocallyTorsion F → IsLocallyTorsion ((lowerShriek f).obj F))

end Sheaf

section Derived

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
  [LocallyOfFiniteType f]
variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/- Remark 63.7.2: Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. Let `Λ` be a ring. The functor
`f_! = lowerShriekModuleDerived : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of
Lemma 63.7.1 sends complexes with torsion cohomology sheaves to complexes
with torsion cohomology sheaves. This is immediate from the description of
the stalks of `f_!`, see Lemma 63.4.5. -/
@[stacks 0GJX] #check
  (AlgebraicGeometry.Scheme.Etale.lowerShriekModuleDerived_etaleDerivedIsTorsion f Λ :
    ∀ (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))),
      etaleDerivedIsTorsion K →
        etaleDerivedIsTorsion ((lowerShriekModuleDerived f Λ).obj K))

end Derived

end AlgebraicGeometry.Scheme.Etale

end
