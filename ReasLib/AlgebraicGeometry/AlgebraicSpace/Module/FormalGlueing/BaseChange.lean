/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalGlueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-! # Base change of reverse formal-glueing kernels -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

/-- Pullback transports an overlap morphism through the canonical composition and restriction maps. -/
def pulledBackφ {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    (pullback (restrictF (f' f g) (i' i g))).obj
        ((pullback (complementBaseChange i g)).obj H) ⟶
      restrict ((pullback (toY f g)).obj G)
        (j' (f' f g) (i' i g)) :=
  (pullbackCompIso (restrictF (f' f g) (i' i g))
      (complementBaseChange i g)).hom.app H ≫
    eqToHom (congrArg (fun h ↦ (pullback h).obj H)
      (overlapBaseChange_comp_restrictF f i g).symm) ≫
    (pullbackCompIso (overlapBaseChange f i g) (restrictF f i)).inv.app H ≫
    (pullback (overlapBaseChange f i g)).map φ ≫
    (pullback (overlapBaseChange f i g)).map
      ((restrictFunctorIsoPullback (j' f i)).hom.app G) ≫
    (pullbackCompIso (overlapBaseChange f i g) (j' f i)).hom.app G ≫
    eqToHom (congrArg (fun h ↦ (pullback h).obj G) (overlapBaseChange_comp_j' f i g)) ≫
    (pullbackCompIso (j' (f' f g) (i' i g))
      (toY f g)).inv.app G ≫
    (restrictFunctorIsoPullback
      (j' (f' f g) (i' i g))).inv.app
      ((pullback (toY f g)).obj G)

section

variable {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
variable (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
variable {H H' : (U i).Modules} {G G' : Y.Modules}
variable (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i))
variable (φ' : (pullback (restrictF f i)).obj H' ⟶ restrict G' (j' f i))
variable (a : H ⟶ H') (b : G ⟶ G')
variable (w : (pullback (restrictF f i)).map a ≫ φ' =
  φ ≫ (restrictFunctor (j' f i)).map b)

include w in
/-- Transport of overlap morphisms respects compatible component maps. -/
theorem pulledBackφ_naturality :
    (pullback (restrictF (f' f g) (i' i g))).map
        ((pullback (complementBaseChange i g)).map a) ≫ pulledBackφ f i g H' G' φ' =
      pulledBackφ f i g H G φ ≫
        (restrictFunctor (j' (f' f g) (i' i g))).map ((pullback (toY f g)).map b) :=
  sorry

end

/-- The canonical pushforward base-change maps send the pulled-back kernel to the new kernel. -/
private theorem reverseBaseChangeHom_condition {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    ((pullback g).map (kernel.ι (comparison f i H G φ)) ≫
      biprod.lift ((pullback g).map biprod.fst) ((pullback g).map biprod.snd) ≫
      biprod.map ((Modules.baseChange (complementBaseChange_comp i g)).app H)
        ((Modules.baseChange (IsPullback.of_hasPullback f g).w).app G)) ≫
      (comparison (f' f g) (i' i g)
      ((pullback (complementBaseChange i g)).obj H)
      ((pullback (toY f g)).obj G) (pulledBackφ f i g H G φ)) = 0 :=
  sorry

/-- The reverse-kernel base-change map is induced by the canonical two pushforward comparisons. -/
@[no_expose] def reverseBaseChangeHom {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    (pullback g).obj (reverse f i H G φ) ⟶
      reverse (f' f g) (i' i g)
        ((pullback (complementBaseChange i g)).obj H)
        ((pullback (toY f g)).obj G) (pulledBackφ f i g H G φ) :=
  kernel.lift
    (comparison (f' f g) (i' i g)
      ((pullback (complementBaseChange i g)).obj H)
      ((pullback (toY f g)).obj G) (pulledBackφ f i g H G φ))
    ((pullback g).map (kernel.ι (comparison f i H G φ)) ≫
      biprod.lift ((pullback g).map biprod.fst) ((pullback g).map biprod.snd) ≫
      biprod.map ((Modules.baseChange (complementBaseChange_comp i g)).app H)
        ((Modules.baseChange (IsPullback.of_hasPullback f g).w).app G))
    (reverseBaseChangeHom_condition f i g H G φ)

/-- Composing the reverse base-change map with the kernel inclusion gives its canonical biproduct map. -/
theorem reverseBaseChangeHom_eq {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    reverseBaseChangeHom f i g H G φ ≫
        kernel.ι (comparison (f' f g) (i' i g)
          ((pullback (complementBaseChange i g)).obj H)
          ((pullback (toY f g)).obj G) (pulledBackφ f i g H G φ)) =
      (pullback g).map (kernel.ι (comparison f i H G φ)) ≫
        biprod.lift ((pullback g).map biprod.fst) ((pullback g).map biprod.snd) ≫
        biprod.map ((Modules.baseChange (complementBaseChange_comp i g)).app H)
          ((Modules.baseChange (IsPullback.of_hasPullback f g).w).app G) :=
  by
    exact kernel.lift_ι _ _ _

section

variable {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
variable (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
variable {H H' : (U i).Modules} {G G' : Y.Modules}
variable (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i))
variable (φ' : (pullback (restrictF f i)).obj H' ⟶ restrict G' (j' f i))
variable (a : H ⟶ H') (b : G ⟶ G')
variable (w : (pullback (restrictF f i)).map a ≫ φ' =
  φ ≫ (restrictFunctor (j' f i)).map b)

/-- The reverse-kernel base-change comparison is natural in compatible component morphisms. -/
theorem reverseBaseChangeHom_naturality :
    (pullback g).map (reverseMap f i φ φ' a b w) ≫
        reverseBaseChangeHom f i g H' G' φ' =
      reverseBaseChangeHom f i g H G φ ≫
        reverseMap (f' f g) (i' i g)
          (pulledBackφ f i g H G φ) (pulledBackφ f i g H' G' φ')
          ((pullback (complementBaseChange i g)).map a) ((pullback (toY f g)).map b)
          (pulledBackφ_naturality f i g φ φ' a b w) :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

namespace AlgebraicGeometry.AlgebraicSpace

open Modules.FormalGlueing

/-- Flat base change commutes with the reverse kernel of a quasi-coherent formal-glueing triple. -/
instance reverseBaseChange_isIso {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] [Flat g] (H : (U i).Modules) (G : Y.Modules)
    (φ : (Modules.pullback (restrictF f i)).obj H ⟶ restrict G (j' f i))
    [H.IsQuasicoherent] [G.IsQuasicoherent] [IsIso φ] :
    IsIso (reverseBaseChangeHom f i g H G φ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
