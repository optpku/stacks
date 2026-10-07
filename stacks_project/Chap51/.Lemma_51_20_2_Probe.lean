module

import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Module
import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Noetherian
import stacks_project.Chap51.Lemma_51_20_2_ResolutionClass

open CategoryTheory CategoryTheory.Abelian

universe u

#check CategoryTheory.ModuleCat.IsMPseudoCoherent
#check @CategoryTheory.ProjectiveResolution.resolutionImageExtClass
#check @CategoryTheory.Abelian.Ext.mk₀
#check @CategoryTheory.Abelian.Ext.comp

variable {R : Type u} [CommRing R]

#synth CategoryTheory.HasExt.{u} (ModuleCat.{u} R)

example (M : ModuleCat.{u} R) : Prop := M.IsMPseudoCoherent 0

example {M M' : ModuleCat.{u} R} (α : M ⟶ M')
    (P' : CategoryTheory.ProjectiveResolution M') (e : ℕ) : Prop :=
  ((CategoryTheory.Abelian.Ext.mk₀.{u} α).comp
    (P'.resolutionImageExtClass e) (zero_add (e + 1)) = 0)
