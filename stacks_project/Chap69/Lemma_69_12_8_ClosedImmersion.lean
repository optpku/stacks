module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.KernelAnnihilation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap69.Definition_69_12_1_Instances

/-!
# Coherent modules along closed immersions of algebraic spaces

This leaf restricts module pushforward along a closed immersion of locally
Noetherian algebraic spaces to coherent modules annihilated by the kernel
ideal sheaf of the immersion.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The category of coherent `𝒪_X`-modules on an algebraic space. -/
abbrev Coh {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (SheafOfModules.isCoherent (structureSheaf X)).FullSubcategory

namespace Coh

/-- The inclusion of coherent modules into all module sheaves on `X`. -/
abbrev inclusion {S : Scheme.{u}} (X : AlgebraicSpace S) : Coh X ⥤ Modules X :=
  (SheafOfModules.isCoherent (structureSheaf X)).ι

end Coh

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
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules) [G.IsCoherent] :
    ((pushforward i).obj G).IsCoherent :=
  sorry

/-- Coherence of the ambient pushforward of an object of `Coh Z`. -/
theorem pushforward_comp_ι_obj_isCoherent
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Coh Z) :
    (((SheafOfModules.isCoherent (structureSheaf Z)).ι ⋙ pushforward i).obj G).IsCoherent :=
  sorry

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
      (pushforward_comp_ι_obj_isCoherent i))
    fun G ↦ pushforward_obj_isAnnihilatedByKernel i G.obj

/-- The underlying module of coherent pushforward is the ordinary pushforward
module. -/
@[simp]
theorem coherentPushforward_obj_obj
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Coh Z) :
    ((coherentPushforward i).obj G).obj.obj = (pushforward i).obj G.obj :=
  sorry

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
