/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom

/-!
# Restriction of comparisons of algebraic-space lifts

Comparisons over a common algebraic space restrict to inverse images by whiskering
and canonical composition transports for the associated groupoid fibrations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Bicategory FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}}

variable {X X' : GroupoidsOver S}
variable {W W' W'' : AlgebraicSpace S}
variable {x : W.toGroupoids ⟶ X}
variable {x' : W'.toGroupoids ⟶ X'}
variable {x'' : W''.toGroupoids ⟶ X'}
variable {iX : X ⟶ X'}
variable {i : W ⟶ W'} {i'' : W ⟶ W''}

/-- The comparison over `W` obtained by composing two diagram isomorphisms
as `α'.symm ≪≫ α''`. -/
def overWIso (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'') :
    AlgebraicSpace.toGroupoids.map i ≫ x' ≅
      AlgebraicSpace.toGroupoids.map i'' ≫ x'' :=
  α'.symm ≪≫ α''

/-- `overWIso` is the pasting `α'.symm ≪≫ α''`. -/
theorem overWIso_spec (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'') :
    overWIso α' α'' = α'.symm ≪≫ α'' :=
  sorry

section InverseImage

variable {U : AlgebraicSpace S} {f' : U ⟶ W'} {f'' : U ⟶ W''}

/-- Restriction of a 2-cell `γ : toGroupoids.map f'' ≫ x'' ≅ toGroupoids.map f' ≫ x'`
to the inverse image `(f')⁻¹(W)`, as left whiskering by
`toGroupoids.map (pullback.snd i f')` reassociated to a binary composite. -/
def restrictGamma
    (γ : AlgebraicSpace.toGroupoids.map f'' ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map f' ≫ x') :
    (AlgebraicSpace.toGroupoids.map (pullback.snd i f') ≫
        AlgebraicSpace.toGroupoids.map f'') ≫ x'' ≅
      (AlgebraicSpace.toGroupoids.map (pullback.snd i f') ≫
        AlgebraicSpace.toGroupoids.map f') ≫ x' :=
  (α_ (AlgebraicSpace.toGroupoids.map (pullback.snd i f'))
      (AlgebraicSpace.toGroupoids.map f'') x'').symm ≪≫
    whiskerLeftIso (AlgebraicSpace.toGroupoids.map (pullback.snd i f')) γ ≪≫
    α_ (AlgebraicSpace.toGroupoids.map (pullback.snd i f'))
      (AlgebraicSpace.toGroupoids.map f') x'

/-- `restrictGamma` is left whiskering of `γ` by
`toGroupoids.map (pullback.snd i f')`, reassociated to a binary composite. -/
theorem restrictGamma_spec
    (γ : AlgebraicSpace.toGroupoids.map f'' ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map f' ≫ x') :
    restrictGamma γ =
      (α_ (AlgebraicSpace.toGroupoids.map (pullback.snd i f'))
          (AlgebraicSpace.toGroupoids.map f'') x'').symm ≪≫
        whiskerLeftIso (AlgebraicSpace.toGroupoids.map (pullback.snd i f')) γ ≪≫
        α_ (AlgebraicSpace.toGroupoids.map (pullback.snd i f'))
          (AlgebraicSpace.toGroupoids.map f') x' :=
  sorry

/-- Restriction of the inverse of the over-`W` comparison to `(f')⁻¹(W)`, transported
along `pullback.condition` and the inverse-image commuting equality so that it
lands in the same 2-cell type as `restrictGamma`. -/
def restrictOverW (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (h_comm : pullback.fst i f' ≫ i'' = pullback.snd i f' ≫ f'') :
    (AlgebraicSpace.toGroupoids.map (pullback.snd i f') ≫
        AlgebraicSpace.toGroupoids.map f'') ≫ x'' ≅
      (AlgebraicSpace.toGroupoids.map (pullback.snd i f') ≫
        AlgebraicSpace.toGroupoids.map f') ≫ x' :=
  whiskerRightIso
      (eqToIso (AlgebraicSpace.toGroupoids.map_comp (pullback.snd i f') f'')).symm x'' ≪≫
    whiskerRightIso (eqToIso (congrArg AlgebraicSpace.toGroupoids.map h_comm.symm)) x'' ≪≫
    whiskerRightIso (eqToIso (AlgebraicSpace.toGroupoids.map_comp (pullback.fst i f') i'')) x'' ≪≫
    α_ (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
      (AlgebraicSpace.toGroupoids.map i'') x'' ≪≫
    whiskerLeftIso (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
      (overWIso α' α'').symm ≪≫
    (α_ (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
      (AlgebraicSpace.toGroupoids.map i) x').symm ≪≫
    whiskerRightIso (eqToIso (AlgebraicSpace.toGroupoids.map_comp (pullback.fst i f') i)).symm x' ≪≫
    whiskerRightIso (eqToIso (congrArg AlgebraicSpace.toGroupoids.map
      (pullback.condition : pullback.fst i f' ≫ i = pullback.snd i f' ≫ f'))) x' ≪≫
    whiskerRightIso (eqToIso (AlgebraicSpace.toGroupoids.map_comp (pullback.snd i f') f')) x'

/-- `restrictOverW` is the transport of left whiskering of `overWIso.symm` along
the inverse-image commuting equality and `pullback.condition`. -/
theorem restrictOverW_spec (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (h_comm : pullback.fst i f' ≫ i'' = pullback.snd i f' ≫ f'') :
    restrictOverW α' α'' h_comm =
      whiskerRightIso
          (eqToIso (AlgebraicSpace.toGroupoids.map_comp (pullback.snd i f') f'')).symm x'' ≪≫
        whiskerRightIso (eqToIso (congrArg AlgebraicSpace.toGroupoids.map h_comm.symm)) x'' ≪≫
        whiskerRightIso (eqToIso (AlgebraicSpace.toGroupoids.map_comp (pullback.fst i f') i'')) x'' ≪≫
        α_ (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
          (AlgebraicSpace.toGroupoids.map i'') x'' ≪≫
        whiskerLeftIso (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
          (overWIso α' α'').symm ≪≫
        (α_ (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
          (AlgebraicSpace.toGroupoids.map i) x').symm ≪≫
        whiskerRightIso (eqToIso (AlgebraicSpace.toGroupoids.map_comp (pullback.fst i f') i)).symm x' ≪≫
        whiskerRightIso (eqToIso (congrArg AlgebraicSpace.toGroupoids.map
          (pullback.condition : pullback.fst i f' ≫ i = pullback.snd i f' ≫ f'))) x' ≪≫
        whiskerRightIso (eqToIso (AlgebraicSpace.toGroupoids.map_comp (pullback.snd i f') f')) x' :=
  sorry

/-- The restriction of `γ` to `(f')⁻¹(W)` equals the transported inverse of
the comparison over `W`. -/
def RestrictsToOverW (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (γ : AlgebraicSpace.toGroupoids.map f'' ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map f' ≫ x')
    (h_comm : pullback.fst i f' ≫ i'' = pullback.snd i f' ≫ f'') : Prop :=
  restrictGamma γ = restrictOverW α' α'' h_comm

/-- `RestrictsToOverW` is equality of `restrictGamma` with `restrictOverW`. -/
theorem RestrictsToOverW_iff (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (γ : AlgebraicSpace.toGroupoids.map f'' ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map f' ≫ x')
    (h_comm : pullback.fst i f' ≫ i'' = pullback.snd i f' ≫ f'') :
    RestrictsToOverW α' α'' γ h_comm ↔ restrictGamma γ = restrictOverW α' α'' h_comm :=
  sorry

end InverseImage

end AlgebraicGeometry.AlgebraicStack.Lift
