/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.FirstOrder
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Restriction

/-!
# Base change for the first principal-parts sequence

The base-change maps on relative differentials, module sheaves, and principal parts form a
morphism from the canonical first principal-parts sequence to the restricted target sequence.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.FirstOrder.BaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {phi : O₁ ⟶ O₂}
variable {phi' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
variable {F : ringedSiteModuleCategory J O₂}
variable {F' : ringedSiteModuleCategory J O₂'}

namespace Presentation

/-- The base-change morphism on the sheafified cotangent presentation of the first
principal-parts sequence. -/
noncomputable def cotangentMap (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') :
    FirstOrder.Presentation.cotangent phi F ⟶
      (restrictionAlong b).obj (FirstOrder.Presentation.cotangent phi' F') :=
  ModuleSheafification.mapToRestriction b
    (PresheafOfModules.Monoidal.tensorHom
        (RelativeDifferentials.presheafMap sq)
        alpha.val ≫
      PresheafOfModules.Restriction.tensorComparison b.hom
        (relativeDifferentials' phi'.hom) F'.val)

/-- The presentation-level cotangent base-change map commutes with the left arrow of the first
principal-parts sequence. -/
theorem cotangent_square (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') :
    CommSq
      (cotangentMap sq alpha)
      (FirstOrder.Presentation.cotangentTo phi F)
      ((restrictionAlong b).map (FirstOrder.Presentation.cotangentTo phi' F'))
      (PrincipalParts.BaseChange.map sq alpha 1) := sorry

end Presentation

/-- The principal-parts base-change map commutes with the projection to the module sheaf. -/
theorem projection_square (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') :
    CommSq
      (PrincipalParts.BaseChange.map sq alpha 1)
      (FirstOrder.projection phi F)
      ((restrictionAlong b).map (FirstOrder.projection phi' F'))
      alpha := sorry

namespace Presentation

/-- The low-assumption base-change morphism between the sheafified-presentation first-order
sequences. -/
noncomputable def sequenceMap (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') :
    FirstOrder.Presentation.sequence phi F ⟶
      (FirstOrder.Presentation.sequence phi' F').map (restrictionAlong b) :=
  ShortComplex.Hom.mk
    (cotangentMap sq alpha)
    (PrincipalParts.BaseChange.map sq alpha 1)
    alpha
    (cotangent_square sq alpha).w
    (projection_square sq alpha).w

/-- Presentation-level base change of the first principal-parts sequence preserves composition
of ring squares and compatible module-sheaf morphisms. -/
@[simp]
theorem sequenceMap_comp
    {O₁'' O₂'' : Sheaf J CommRingCat.{max u v}}
    {a' : O₁' ⟶ O₁''} {phi'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq : CommSq a phi phi' b) (sq' : CommSq a' phi' phi'' b')
    {F'' : ringedSiteModuleCategory J O₂''}
    (alpha : F ⟶ (restrictionAlong b).obj F')
    (alpha' : F' ⟶ (restrictionAlong b').obj F'') :
    sequenceMap (CommSq.horiz_comp sq sq')
        (alpha ≫ (restrictionAlong b).map alpha') =
      sequenceMap sq alpha ≫
        (restrictionAlong b).mapShortComplex.map (sequenceMap sq' alpha') := sorry

end Presentation

section CanonicalTensor

/-- The canonical base-change morphism on the cotangent term
`Ω(phi) ⊗ F` of the first principal-parts sequence. -/
noncomputable def cotangentMap (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') :
    FirstOrder.cotangentTensor phi F ⟶
      (restrictionAlong b).obj (FirstOrder.cotangentTensor phi' F') :=
  moduleTensorMap
      (RelativeDifferentials.map sq) alpha ≫
    Restriction.tensorComparison b (relativeDifferentials phi') F'

/-- The cotangent base-change map commutes with the left arrow of the first principal-parts
sequence. -/
theorem cotangent_square (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') :
    CommSq
      (cotangentMap sq alpha)
      (FirstOrder.cotangentTo phi F)
      ((restrictionAlong b).map (FirstOrder.cotangentTo phi' F'))
      (PrincipalParts.BaseChange.map sq alpha 1) := sorry

/-- Tag 0G3W: base change of principal parts is compatible with the canonical first-order
sequence. -/
@[stacks 0G3W "base change of the first principal-parts sequence"]
noncomputable def sequenceMap (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') :
    FirstOrder.sequence phi F ⟶
      (FirstOrder.sequence phi' F').map (restrictionAlong b) :=
  ShortComplex.Hom.mk
    (cotangentMap sq alpha)
    (PrincipalParts.BaseChange.map sq alpha 1)
    alpha
    (cotangent_square sq alpha).w
    (projection_square sq alpha).w

/-- The comparison between the canonical and presentation first-principal-parts sequences is
natural with respect to base change. -/
@[stacks 0G3W "naturality of the first-order presentation comparison"]
theorem sequenceIso_naturality (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') :
    sequenceMap sq alpha ≫
        (restrictionAlong b).mapShortComplex.map
          (FirstOrder.sequenceIso phi' F').hom =
      (FirstOrder.sequenceIso phi F).hom ≫ Presentation.sequenceMap sq alpha := sorry

/-- Base change of the canonical first principal-parts sequence preserves composition of ring
squares and compatible module-sheaf morphisms. -/
@[simp]
theorem sequenceMap_comp
    {O₁'' O₂'' : Sheaf J CommRingCat.{max u v}}
    {a' : O₁' ⟶ O₁''} {phi'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq : CommSq a phi phi' b) (sq' : CommSq a' phi' phi'' b')
    {F'' : ringedSiteModuleCategory J O₂''}
    (alpha : F ⟶ (restrictionAlong b).obj F')
    (alpha' : F' ⟶ (restrictionAlong b').obj F'') :
    sequenceMap (CommSq.horiz_comp sq sq')
        (alpha ≫ (restrictionAlong b).map alpha') =
      sequenceMap sq alpha ≫
        (restrictionAlong b).mapShortComplex.map (sequenceMap sq' alpha') := sorry

end CanonicalTensor

end SheafOfModules.RingedSite.PrincipalParts.FirstOrder.BaseChange
