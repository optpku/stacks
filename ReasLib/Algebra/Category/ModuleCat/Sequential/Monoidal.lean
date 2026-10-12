/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sequential.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal
public import ReasLib.CategoryTheory.Sites.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products on sequential varying-ring modules

@stack 091H

The bottom-topology presentation of a sequential varying-ring module category is the module
category of a commutative ring sheaf.  This file installs the corresponding symmetric additive
tensor structure and the colimit conditions used by Koszul totalization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory.SequentialInverseSystem

/-- The commutative-ring sheaf underlying a sequential inverse system on the bottom topology. -/
@[stacks 091H "bottom-topology commutative-ring sheaf"]
abbrev bottomCommRingSheaf (F : SequentialInverseSystem CommRingCat.{u}) :
    Sheaf (⊥ : GrothendieckTopology Nat) CommRingCat.{u} :=
  ⟨F, Presheaf.isSheaf_bot F⟩

/-- Sequential varying-ring modules carry the tensor product obtained from module sheaves on the
bottom ringed site. -/
@[stacks 091H "tensor product on sequential varying-ring modules", reducible]
noncomputable instance moduleSystemMonoidalCategory
    (F : SequentialInverseSystem CommRingCat.{u}) :
    MonoidalCategory (ModuleSystem.{u, u} F) :=
  SheafOfModules.RingedSite.moduleMonoidalCategory (bottomCommRingSheaf F)

/-- The tensor product on sequential varying-ring modules is symmetric. -/
@[stacks 091H "symmetric tensor on sequential varying-ring modules", reducible]
noncomputable instance moduleSystemSymmetricCategory
    (F : SequentialInverseSystem CommRingCat.{u}) :
    SymmetricCategory (ModuleSystem.{u, u} F) :=
  SheafOfModules.RingedSite.moduleSymmetricCategory (bottomCommRingSheaf F)

/-- The tensor product on sequential varying-ring modules is additive in both variables. -/
@[stacks 091H "additive tensor on sequential varying-ring modules"]
noncomputable instance moduleSystemMonoidalPreadditive
    (F : SequentialInverseSystem CommRingCat.{u}) :
    MonoidalPreadditive (ModuleSystem.{u, u} F) :=
  SheafOfModules.RingedSite.monoidalPreadditive
    (J := (⊥ : GrothendieckTopology Nat)) (O := bottomCommRingSheaf F)

/-- The first parenthesization of three graded sequential module systems is compatible with
Koszul totalization. -/
@[stacks 091H "left-associated graded tensor compatibility"]
noncomputable instance moduleSystemHasGoodTensor12
    (F : SequentialInverseSystem CommRingCat.{u})
    (G1 G2 G3 : GradedObject Int (ModuleSystem.{u, u} F)) :
    GradedObject.HasGoodTensor₁₂Tensor G1 G2 G3 := sorry

/-- The second parenthesization of three graded sequential module systems is compatible with
Koszul totalization. -/
@[stacks 091H "right-associated graded tensor compatibility"]
noncomputable instance moduleSystemHasGoodTensor23
    (F : SequentialInverseSystem CommRingCat.{u})
    (G1 G2 G3 : GradedObject Int (ModuleSystem.{u, u} F)) :
    GradedObject.HasGoodTensorTensor₂₃ G1 G2 G3 := sorry

/-- Fourfold graded tensors of sequential module systems satisfy the extensionality condition
used by the Koszul associator. -/
@[stacks 091H "fourfold graded tensor extensionality"]
noncomputable instance moduleSystemHasTensor4ObjExt
    (F : SequentialInverseSystem CommRingCat.{u})
    (G1 G2 G3 G4 : GradedObject Int (ModuleSystem.{u, u} F)) :
    GradedObject.HasTensor₄ObjExt G1 G2 G3 G4 := sorry

end CategoryTheory.SequentialInverseSystem
