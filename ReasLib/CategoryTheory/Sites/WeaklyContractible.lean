/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Cover
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly contractible objects of a site

This module owns the section-surjectivity formulation of weak contractibility and its canonical
cover-map characterization.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- An object is weakly contractible when every locally surjective morphism of sheaves of sets is
surjective on its sections over that object. -/
@[stacks 090L "(1)"]
class IsWeaklyContractible (U : C) : Prop where
  /-- Every locally surjective sheaf map is surjective on sections over `U`. -/
  surjective_sections {F G : Sheaf J (Type (max u v))}
      (pi : F ⟶ G) (_ : Sheaf.IsLocallySurjective pi) :
      Function.Surjective (pi.hom.app (op U))

section

variable [HasWeakSheafify J (Type (max u v))]

namespace IsWeaklyContractible

/-- An object is weakly contractible exactly when every canonical sheafified cover
map onto its representable sheaf is split epic. -/
@[stacks 090K]
theorem iff_isSplitEpi_coverMap (U : C) :
    J.IsWeaklyContractible U <->
      forall S : J.Cover U, IsSplitEpi (J.sheafifiedRepresentableCoverMap S) := sorry

/-- A weakly contractible object splits every canonical sheafified cover map onto its
representable sheaf. -/
theorem isSplitEpi_coverMap {U : C} [J.IsWeaklyContractible U] (S : J.Cover U) :
    IsSplitEpi (J.sheafifiedRepresentableCoverMap S) := sorry

/-- Splittings of all canonical sheafified cover maps imply weak contractibility. -/
theorem of_isSplitEpi_coverMap {U : C}
    (hU : forall S : J.Cover U, IsSplitEpi (J.sheafifiedRepresentableCoverMap S)) :
    J.IsWeaklyContractible U := sorry

/-- An object whose canonical sheafified cover maps are all split epic is weakly contractible. -/
instance instOfSplitCoverMaps {U : C}
    [∀ cover : J.Cover U, IsSplitEpi (J.sheafifiedRepresentableCoverMap cover)] :
    J.IsWeaklyContractible U := sorry

end IsWeaklyContractible

end

end CategoryTheory.GrothendieckTopology
