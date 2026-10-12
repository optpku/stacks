/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Scheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent

/-!
# Coherent modules along closed immersions

This leaf restricts the module-pushforward equivalence for a closed immersion to coherent
modules on locally Noetherian schemes. The underlying annihilation predicate and equivalence
for all module sheaves remain owned by the more general ringed-space API.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ClosedImmersion

variable {X Z : Scheme.{u}}

/-- The property of a coherent module on `X` that is annihilated by the kernel of the
structure-sheaf map associated to `i : Z ⟶ X`. -/
abbrev coherentAnnihilated (i : Z ⟶ X) :
    ObjectProperty (RingedSpace.Coh X.toRingedSpace) :=
  fun M ↦ SheafOfModules.IsAnnihilatedByKernel
    (RingedSpace.Hom.toRingCatSheafHom i.toShHom) M.obj

/-- The category of coherent modules annihilated by the kernel ideal of `i : Z ⟶ X`. -/
abbrev CoherentAnnihilatedModules (i : Z ⟶ X) :=
  (coherentAnnihilated i).FullSubcategory

/-- Kernel annihilation of a coherent module is equivalent to the defining ideal sheaf acting
as zero on all local sections. -/
theorem coherentAnnihilated_iff (i : Z ⟶ X) (M : RingedSpace.Coh X.toRingedSpace) :
    coherentAnnihilated i M ↔
      ∀ U : Opens X,
        ∀ s : (RingedSpace.Hom.idealSheaf i.toShHom).val.obj (op U),
          ∀ m : M.obj.val.obj (op U),
            ((RingedSpace.Hom.idealSheafι i.toShHom).val.app (op U) s) • m = 0 := sorry

/-- Pushforward along a closed immersion of locally Noetherian schemes carries coherent modules
to coherent modules. -/
theorem pushforward_obj_isCoherent
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : RingedSpace.Coh Z.toRingedSpace) :
    (((SheafOfModules.isCoherent Z.ringCatSheaf).ι ⋙ pushforward i).obj G).IsCoherent := sorry

/-- Pushforward of coherent modules along a closed immersion, restricted to coherent modules
annihilated by the kernel ideal. -/
noncomputable def coherentPushforward
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    RingedSpace.Coh Z.toRingedSpace ⥤ CoherentAnnihilatedModules i :=
  ObjectProperty.lift (coherentAnnihilated i)
    (ObjectProperty.lift (SheafOfModules.isCoherent X.ringCatSheaf)
      ((SheafOfModules.isCoherent Z.ringCatSheaf).ι ⋙ pushforward i)
      (pushforward_obj_isCoherent i))
    (fun G ↦ SheafOfModules.IsAnnihilatedByKernel.of_pushforward
      (RingedSpace.Hom.toRingCatSheafHom i.toShHom) G.obj)

/-- The underlying module of coherent pushforward is the ordinary pushforward module. -/
@[simp]
theorem coherentPushforward_obj_obj
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : RingedSpace.Coh Z.toRingedSpace) :
    ((coherentPushforward i).obj G).obj.obj = (pushforward i).obj G.obj := sorry

/-- Coherent pushforward along a closed immersion of locally Noetherian schemes is an
equivalence onto the coherent modules annihilated by its kernel ideal. -/
noncomputable instance coherentPushforward_isEquivalence
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (coherentPushforward i).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.Modules.ClosedImmersion
