/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.LargestSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasicoherent modules along closed immersions

This file owns the exceptional inverse image on quasicoherent modules along a closed immersion
and its adjunction with pushforward.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {X Z : Scheme.{u}}

/-- Pushforward of quasicoherent modules along a closed immersion is exact. -/
theorem pushforwardExact (i : Z ⟶ X) [IsClosedImmersion i] :
    exactFunctor (QCoh Z) (QCoh X) (pushforward i) := sorry

/-- Pushforward along a closed immersion induces a bijection on morphisms between
quasicoherent modules. -/
theorem pushforward_map_bijective (i : Z ⟶ X) [IsClosedImmersion i] (F G : QCoh Z) :
    Function.Bijective (fun f : F ⟶ G ↦ (pushforward i).map f) := sorry

/-- A quasicoherent module lies in the essential image of pushforward along a closed immersion
exactly when every local section of the defining ideal sheaf acts by zero. -/
theorem mem_essImage_iff_idealSheaf_smul_eq_zero
    (i : Z ⟶ X) [IsClosedImmersion i] (G : QCoh X) :
    (pushforward i).essImage G ↔
      ∀ U : X.Opens,
        ∀ s : (RingedSpace.Hom.idealSheaf i.toShHom).val.obj (op U),
          ∀ m : G.obj.val.obj (op U),
            ((RingedSpace.Hom.idealSheafι i.toShHom).val.app (op U) s) • m = 0 := sorry

/-- Pushforward of quasicoherent modules along a closed immersion admits a right adjoint. -/
@[stacks 01R0, instance]
theorem pushforward_isLeftAdjoint (i : Z ⟶ X) [IsClosedImmersion i] :
    (pushforward i).IsLeftAdjoint := sorry

/-- The exceptional inverse image on quasicoherent modules along a closed immersion. -/
noncomputable def shriek (i : Z ⟶ X) [IsClosedImmersion i]
    [(pushforward i).IsLeftAdjoint] :
    QCoh X ⥤ QCoh Z :=
  (pushforward i).rightAdjoint

/-- The canonical adjunction between closed-immersion pushforward and exceptional inverse
image. -/
noncomputable def pushforwardShriekAdjunction (i : Z ⟶ X) [IsClosedImmersion i]
    [(pushforward i).IsLeftAdjoint] :
    pushforward i ⊣ shriek i :=
  Adjunction.ofIsLeftAdjoint (pushforward i)

end AlgebraicGeometry.Scheme.QCoh
