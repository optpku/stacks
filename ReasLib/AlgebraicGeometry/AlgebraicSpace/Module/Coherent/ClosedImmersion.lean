/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.KernelAnnihilation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf

/-!
# Coherent modules along closed immersions of algebraic spaces

Module pushforward restricts along a closed immersion of locally
Noetherian algebraic spaces to coherent modules annihilated by the kernel
ideal sheaf of the immersion.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules.ClosedImmersion

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

/-- The property of a coherent module on `X` that is annihilated by the kernel of
`𝒪_X ⟶ i_* 𝒪_Z`. -/
abbrev coherentAnnihilated (i : Z ⟶ X) : ObjectProperty (Coh X) :=
  fun M ↦ SheafOfModules.IsAnnihilatedByKernel
    (SheafOfModules.ChangeOfRings.homOverId (structureSheafMap i)) M.obj

/-- The category of coherent `𝒪_X`-modules annihilated by the kernel ideal of
`i : Z ⟶ X`. -/
abbrev CoherentAnnihilatedModules (i : Z ⟶ X) :=
  (coherentAnnihilated i).FullSubcategory

/-- Kernel annihilation of a coherent module is equivalent to the associated ideal
sheaf `Hom.idealSheaf i` acting as zero on all local sections. -/
theorem coherentAnnihilated_iff (i : Z ⟶ X) (M : Coh X) :
    coherentAnnihilated i M ↔
      ∀ U : (smallEtaleSite X)ᵒᵖ,
        ∀ s : (Hom.idealSheaf i).val.obj U,
          ∀ m : M.obj.val.obj U,
            ((Hom.idealSheafι i).val.app U s) • m = 0 :=
  sorry

/-- Pushforward along a closed immersion of locally Noetherian algebraic spaces
carries coherent modules to coherent modules. -/
instance pushforward_obj_isCoherent
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules) [hG : G.IsCoherent] :
    ((pushforward i).obj G).IsCoherent :=
  sorry

/-- The pushforward of the structure module along a closed immersion into a locally
Noetherian algebraic space is coherent. -/
instance pushforward_unit_isCoherent
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    ((pushforward i).obj (SheafOfModules.unit (structureSheaf Z))).IsCoherent :=
  @pushforward_obj_isCoherent S Z X inferInstance
    (IsLocallyNoetherian.of_isClosedImmersion i) i inferInstance
    (SheafOfModules.unit (structureSheaf Z))
    (@structureSheaf_isCoherent S Z (IsLocallyNoetherian.of_isClosedImmersion i))

/-- Pushforward of any module sheaf along `i` is annihilated by the kernel of
`𝒪_X ⟶ i_* 𝒪_Z`. -/
theorem pushforward_obj_isAnnihilatedByKernel (i : Z ⟶ X) (G : Z.Modules) :
    SheafOfModules.IsAnnihilatedByKernel
      (SheafOfModules.ChangeOfRings.homOverId (structureSheafMap i))
      ((pushforward i).obj G) :=
  sorry

/-- Pushforward of coherent modules along a closed immersion, restricted to
coherent modules annihilated by the kernel ideal. -/
noncomputable def coherentPushforward
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    Coh Z ⥤ CoherentAnnihilatedModules i :=
  ObjectProperty.lift (coherentAnnihilated i)
    (ObjectProperty.lift (SheafOfModules.isCoherent (structureSheaf X))
      ((SheafOfModules.isCoherent (structureSheaf Z)).ι ⋙ pushforward i)
      (fun G ↦ pushforward_obj_isCoherent i G.obj (hG := G.property)))
    fun G ↦ pushforward_obj_isAnnihilatedByKernel i G.obj

/-- The underlying module of coherent pushforward is the ordinary pushforward
module. -/
@[simp]
theorem coherentPushforward_obj_obj
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Coh Z) :
    ((coherentPushforward i).obj G).obj.obj = (pushforward i).obj G.obj :=
  rfl

/-- Coherent pushforward along a closed immersion of locally Noetherian algebraic
spaces is an equivalence onto the coherent modules annihilated by its kernel
ideal. -/
noncomputable instance coherentPushforward_isEquivalence
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (coherentPushforward i).IsEquivalence :=
  sorry

end Modules.ClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
