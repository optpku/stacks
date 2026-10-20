/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Topology.Sheaf.ExtensionByInitial

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

/-
The source specializes extension by the initial object to `AddCommGrpCat`, whose initial object is
the zero abelian group. The generic extension-by-initial namespaces are the reusable owner;
the tagged checks below fix `C = AddCommGrpCat` explicitly, preserving the source while avoiding
parallel abelian-only wrappers. The stalk formula is split into its inside and outside branches,
matching the two reusable owner theorems.
-/

section

variable {X : TopCat.{u}} (U : Opens X)

/- Lemma 6.31.6 (1): extension by zero for abelian presheaves on an open subset is left adjoint
to restriction. -/
@[stacks 00A5 "abelian presheaf extension-restriction adjunction"]
#check
  (TopCat.Presheaf.ExtensionByInitial.Properties.adjunction
    (C := AddCommGrpCat.{u}) U)

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/- Lemma 6.31.6 (2): extension by zero for abelian sheaves on an open subset is left adjoint to
restriction; the adjunction gives the stated bifunctorial equivalence of morphisms. -/
@[stacks 00A5 "abelian sheaf extension-restriction adjunction"]
#check
  (TopCat.Sheaf.ExtensionByInitial.Properties.adjunction
    (C := AddCommGrpCat.{u}) U)

variable (ℱ : (TopCat.Opens.Subspace.space U).Sheaf AddCommGrpCat.{u})

/- Lemma 6.31.6 (3), inside `U`: the stalk of the extension-by-zero sheaf is canonically
isomorphic to the original stalk. -/
@[stacks 00A5 "stalk of abelian extension by zero inside the open subset"]
#check fun (x : TopCat.Opens.Subspace.space U) ↦
  TopCat.Sheaf.ExtensionByInitial.Properties.stalkIso_of_mem U ℱ x

/- Lemma 6.31.6 (3), outside `U`: the stalk of the extension-by-zero sheaf is the zero abelian
group. -/
@[stacks 00A5 "stalk of abelian extension by zero outside the open subset"]
#check fun (x : X) (hx : x ∉ (U : Set X)) ↦
  TopCat.Sheaf.ExtensionByInitial.Properties.stalk_isInitial_of_not_mem U ℱ x hx

/- Lemma 6.31.6 (4): restriction after extension by zero is naturally isomorphic to the identity
on abelian presheaves over the open subset. -/
@[stacks 00A5 "abelian presheaf restriction after extension by zero"]
#check
  (TopCat.Presheaf.ExtensionByInitial.Properties.unit_isIso
    (C := AddCommGrpCat.{u}) U)

/- Lemma 6.31.6 (5): restriction after extension by zero is naturally isomorphic to the identity
on abelian sheaves over the open subset. -/
@[stacks 00A5 "abelian sheaf restriction after extension by zero"]
#check
  (TopCat.Sheaf.ExtensionByInitial.Properties.unit_isIso
    (C := AddCommGrpCat.{u}) U)

end
