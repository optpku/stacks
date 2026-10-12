/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom
public import stacks_project.Chap59.Lemma_59_40_1_Hom

/-!
# Lemma 59.40.1

The morphism of small étale ringed sites associated to a scheme morphism is a morphism of
locally ringed sites in the sense of Modules on Sites, Definition 18.40.9.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSite.Hom
open Scheme.AssociatedModule

noncomputable section

universe u

namespace Scheme.Etale.Small

variable {X Y : Scheme.{u}}

/-- Lemma 59.40.1: for a morphism of schemes `f : X ⟶ Y`, the associated morphism of small
étale ringed sites `(f_small, f_small^♯)`, packaged as `commRingedHom f`, is a morphism of
locally ringed sites in the sense of Definition 18.40.9, i.e. `RingedSite.Hom.IsLocal`. -/
@[stacks 04I5, instance]
instance commRingedHom_isLocal (f : X ⟶ Y) : (commRingedHom f).IsLocal :=
  sorry

/-- Locality of `commRingedHom f` is objectwise locality of the inverse-image structure-sheaf
map, matching Definition 18.40.9. -/
theorem commRingedHom_isLocal_iff (f : X ⟶ Y) :
    (commRingedHom f).IsLocal ↔
      ∀ U : (smallCommRingedSite .etale X)ᵒᵖ,
        IsLocalHom ((inverseImageStructureSheafMap (commRingedHom f)).hom.app U).hom :=
  sorry

end Scheme.Etale.Small
