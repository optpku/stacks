/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite

/-!
# Upper shriek for étale morphisms

For an étale morphism, finite-support lower shriek is left adjoint to étale
restriction, so its right adjoint is canonically isomorphic to restriction.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/-- Finite-support lower shriek along an étale morphism is left adjoint to
étale restriction, via the canonical comparison with extension by zero. -/
def lowerShriekRestrictionAdjunction :
    lowerShriek j ⊣ etaleRestrictionSheaf j AddCommGrpCat.{u} :=
  (abelianExtensionByZero_adjunction j).ofNatIsoLeft
    (extensionByZeroIsoLowerShriek j)

/-- Any right adjoint of finite-support lower shriek along an étale morphism
is canonically isomorphic to étale restriction. -/
def lowerShriek_rightAdjointIsoRestriction
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf U.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek j ⊣ G) :
    G ≅ etaleRestrictionSheaf j AddCommGrpCat.{u} :=
  adj.rightAdjointUniq (lowerShriekRestrictionAdjunction j)

/-- Non-derived upper shriek along an étale morphism is canonically naturally
isomorphic to inverse image on abelian étale sheaves. -/
def upperShriekIsoRestriction :
    upperShriek j ≅ etaleRestrictionSheaf j AddCommGrpCat.{u} :=
  lowerShriek_rightAdjointIsoRestriction j (lowerShriekAdjunction j)

end AlgebraicGeometry.Scheme.Etale

end
