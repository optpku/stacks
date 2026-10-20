/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Basis.Algebraic.SectionFamilies
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits Opposite TopCat TopologicalSpace

universe w v u u1

section

variable {C : Type u} [Category.{v} C]
variable {F : C ⥤ Type u1} [IsAlgebraicStructure C F]
variable [HasLimitsOfSize.{w, w} C] [PreservesLimitsOfSize.{w, w} F]
variable {X Y : TopCat.{w}} (f : X ⟶ Y)

/-
The resulting `f`-map is canonically a morphism `𝒢 ⟶ (Sheaf.pushforward C f).obj ℱ`, while the
source supplies its components on two independently chosen bases. The neutral owner
`TopCat.Presheaf.BasisPushforwardHomFamily` records exactly this presheaf-level data and its two restriction
compatibilities.
-/

/- Lemma 6.30.16: a compatible family of morphisms `𝒢(V) ⟶ ℱ(U)` for basis opens `V` of `Y`
and `U` of `X` satisfying `U ⊆ f⁻¹(V)` comes from a unique morphism `𝒢 ⟶ f_* ℱ`, and restriction
from `f⁻¹(V)` to `U` recovers the prescribed morphism. -/
@[stacks 009X]
#check
  TopCat.Presheaf.BasisPushforwardHomFamily.existsUniquePushforwardHom f

end
