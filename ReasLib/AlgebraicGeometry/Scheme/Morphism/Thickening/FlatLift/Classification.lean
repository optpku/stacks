/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.FlatLift.Translation
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Torsor
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.MapObstruction

/-!
# Isomorphism classes of flat first-order scheme lifts

Two flat lifts are isomorphic when there is an ambient isomorphism over `S'`
reducing to the identity on `X`. Their classes form a principal homogeneous
space under Ext¹(NL[X/S], f^* 𝒞_{S/S'}), via pushout translation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Thickening
open AlgebraicGeometry.RingedSpace.Thickening (FittingMap homOmegaExtZero homOmegaExtZeroAddEquiv Solution)
open scoped AlgebraicGeometry DerivedExt RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Thickening
namespace FlatLift

variable {S S' X : Scheme.{u}}
variable {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S} [Flat f]

/-- Existence of a morphism of flat lifts is an equivalence relation. -/
private theorem isoRelation_equivalence :
    Equivalence (fun L₁ L₂ : FlatLift t f ↦ Nonempty (Hom L₁ L₂)) := sorry

/-- The setoid identifying flat lifts with an ambient isomorphism over `S'`
reducing to the identity on `X`. -/
@[no_expose] def isoSetoid (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) [Flat f] :
    Setoid (FlatLift t f) where
  r L₁ L₂ := Nonempty (Hom L₁ L₂)
  iseqv := isoRelation_equivalence

/-- Two flat lifts are related iff they have a morphism of lifts. -/
theorem isoSetoid_rel (L₁ L₂ : FlatLift t f) :
    isoSetoid t f L₁ L₂ ↔ Nonempty (Hom L₁ L₂) := by rfl

/-- Isomorphism classes of flat first-order lifts of `f` across `t`. -/
abbrev IsoClass (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) [Flat f] :=
  Quotient (isoSetoid t f)

/-- The isomorphism class of a given flat lift. -/
@[no_expose] def isoClassMk (L : FlatLift t f) : IsoClass t f :=
  Quotient.mk (isoSetoid t f) L

/-- A morphism of flat lifts identifies isomorphism classes. -/
theorem isoClassMk_eq_mk_of_hom {L₁ L₂ : FlatLift t f} (φ : Hom L₁ L₂) :
    isoClassMk L₁ = isoClassMk L₂ := sorry

/-- The obstruction class in Ext¹(NL[f], f^* 𝒞_{S/S'}) comparing two flat lifts,
transported from the identity-cube obstruction of the associated ringed-space
solutions. -/
@[no_expose] def obstruction (L₁ L₂ : FlatLift t f) : extOneNL t f :=
  Solution.obstruction (toSolution L₁) (toSolution L₂)

/-- `obstruction` is the ringed-space identity-cube obstruction of `toSolution`. -/
theorem obstruction_spec (L₁ L₂ : FlatLift t f) :
    obstruction L₁ L₂ = Solution.obstruction (toSolution L₁) (toSolution L₂) := by rfl

/-- The obstruction vanishes iff the two lifts have a morphism of lifts. -/
theorem obstruction_eq_zero_iff (L₁ L₂ : FlatLift t f) :
    obstruction L₁ L₂ = 0 ↔ Nonempty (Hom L₁ L₂) := sorry

/-- Translating a lift by ξ realizes ξ as an obstruction. -/
theorem obstruction_translate (ξ : extOneNL t f) (L : FlatLift t f) :
    obstruction L (translate ξ L) = ξ := sorry

/-- Translation respects isomorphism of flat lifts. -/
private theorem translate_congr (ξ : extOneNL t f) (L₁ L₂ : FlatLift t f)
    (h : isoSetoid t f L₁ L₂) : isoSetoid t f (translate ξ L₁) (translate ξ L₂) := sorry

/-- The obstruction is independent of compatible representatives. -/
private theorem obstruction_congr (A B A' B' : FlatLift t f)
    (hA : isoSetoid t f A A') (hB : isoSetoid t f B B') :
    obstruction B A = obstruction B' A' := sorry

/-- Action of an Ext¹ class on an isomorphism class, via `translate`. -/
@[no_expose] def vadd (ξ : extOneNL t f) (p : IsoClass t f) : IsoClass t f :=
  Quotient.map (translate ξ) (translate_congr ξ) p

/-- Difference of isomorphism classes, as an Ext¹ class. Subtraction is oriented
so that `[X'_ξ] -ᵥ [X'] = ξ` when `o(X', X'_ξ) = ξ`. -/
@[no_expose] def vsub (p q : IsoClass t f) : extOneNL t f :=
  Quotient.lift₂ (fun L₁ L₂ ↦ obstruction L₂ L₁) obstruction_congr p q

/-- Ext¹ classes act on isomorphism classes of flat lifts by translation. -/
instance instVAdd_isoClass : VAdd (extOneNL t f) (IsoClass t f) where
  vadd := vadd

/-- Difference of isomorphism classes of flat lifts is an Ext¹ class. -/
instance instVSub_isoClass : VSub (extOneNL t f) (IsoClass t f) where
  vsub := vsub

/-- The Ext¹-action computes on representatives by `translate`. -/
theorem vadd_mk (ξ : extOneNL t f) (L : FlatLift t f) :
    ξ +ᵥ isoClassMk L = isoClassMk (translate ξ L) := by rfl

/-- Torsor subtraction computes on representatives by the reversed obstruction. -/
theorem vsub_mk (L₁ L₂ : FlatLift t f) :
    isoClassMk L₁ -ᵥ isoClassMk L₂ = obstruction L₂ L₁ := by rfl

/-- The zero Ext¹ class acts as the identity on isomorphism classes. -/
theorem vadd_zero (p : IsoClass t f) :
    (0 : extOneNL t f) +ᵥ p = p := sorry

/-- The Ext¹-action is compatible with addition. -/
theorem add_vadd (ξ η : extOneNL t f) (p : IsoClass t f) :
    (ξ + η) +ᵥ p = ξ +ᵥ η +ᵥ p := sorry

/-- The Ext¹-action of naive cotangent classes on isomorphism classes of flat
lifts. -/
instance instAddAction_isoClass : AddAction (extOneNL t f) (IsoClass t f) where
  add_vadd := add_vadd
  zero_vadd := vadd_zero

/-- Adding the difference of flat-lift classes recovers its first argument. -/
private theorem vsub_vadd (p q : IsoClass t f) : (p -ᵥ q) +ᵥ q = p := sorry

/-- Subtracting a flat-lift class from its translate recovers the parameter. -/
private theorem vadd_vsub (ξ : extOneNL t f) (p : IsoClass t f) :
    (ξ +ᵥ p) -ᵥ p = ξ := sorry

/-- With a chosen flat lift as basepoint, isomorphism classes are an additive
torsor under Ext¹(NL[f], f^* 𝒞_{S/S'}). -/
@[reducible, no_expose] def addTorsor (S0 : FlatLift t f) : AddTorsor (extOneNL t f) (IsoClass t f) where
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := vsub_vadd
  vadd_vsub' := vadd_vsub

/-- A basepoint lift makes the set of isomorphism classes nonempty. -/
theorem addTorsor_nonempty (S0 : FlatLift t f) : Nonempty (IsoClass t f) :=
  (addTorsor S0).nonempty

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The identity connecting cube of the ringed-space solution of a flat lift. -/
private def idCube (L : FlatLift t f) :=
  Solution.compare (toSolution L) (toSolution L)

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The identity map of a flat lift commutes with its inclusion. -/
private theorem idFitting_comm_top (L : FlatLift t f) :
    (toSolution L).i ≫ 𝟙 (toSolution L).space = 𝟙 X.toRingedSpace ≫ (toSolution L).i := sorry

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The identity map of a flat lift commutes with its ambient map. -/
private theorem idFitting_comm_right (L : FlatLift t f) :
    𝟙 (toSolution L).space ≫ (toSolution L).f' = (toSolution L).f' ≫ 𝟙 S'.toRingedSpace := sorry

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The identity map induces the prescribed identity comparison on kernels. -/
private theorem idFitting_induces (L : FlatLift t f) :
    @RingedSpace.Thickening.kernelMapOf _ _ _ (toSolution L).i (toSolution L).i_isFirstOrder
      (𝟙 X.toRingedSpace) _ (toSolution L).i (toSolution L).i_isFirstOrder
      (𝟙 (toSolution L).space) (idFitting_comm_top L) = (@RingedSpace.Thickening.RelativeDiagram.ν _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance (idCube L)) := sorry

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- The identity filling of the identity cube of a flat lift. -/
private def idFitting (L : FlatLift t f) : Solution.Fitting (toSolution L) (toSolution L) :=
  @FittingMap.of _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance (Solution.compare (toSolution L) (toSolution L))
    (𝟙 (toSolution L).space) (idFitting_comm_top L)
    (idFitting_comm_right L) (idFitting_induces L)

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- A reducing-to-identity automorphism commutes with the inclusion. -/
private theorem autoToFitting_comm_top {L : FlatLift t f} (φ : ReduceIdAuto L) :
    (toSolution L).i ≫ φ.hom.toShHom = 𝟙 X.toRingedSpace ≫ (toSolution L).i := sorry

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- A reducing-to-identity automorphism commutes with the ambient map. -/
private theorem autoToFitting_comm_right {L : FlatLift t f} (φ : ReduceIdAuto L) :
    φ.hom.toShHom ≫ (toSolution L).f' = (toSolution L).f' ≫ 𝟙 S'.toRingedSpace := sorry

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- A reducing-to-identity automorphism induces the comparison kernel map. -/
private theorem autoToFitting_induces {L : FlatLift t f} (φ : ReduceIdAuto L) :
    @RingedSpace.Thickening.kernelMapOf _ _ _ (toSolution L).i (toSolution L).i_isFirstOrder
      (𝟙 X.toRingedSpace) _ (toSolution L).i (toSolution L).i_isFirstOrder
      φ.hom.toShHom (autoToFitting_comm_top φ) = (@RingedSpace.Thickening.RelativeDiagram.ν _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance (idCube L)) := sorry

-- Local declaration justification (module visibility): export this private dependency
-- so the dependent public constructions can use it without publishing its name.
set_option backward.privateInPublic true in
/-- Convert a reducing-to-identity automorphism into a compatible filling. -/
private def autoToFitting {L : FlatLift t f} (φ : ReduceIdAuto L) :
    Solution.Fitting (toSolution L) (toSolution L) :=
  @FittingMap.of _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance (Solution.compare (toSolution L) (toSolution L))
    φ.hom.toShHom (autoToFitting_comm_top φ)
    (autoToFitting_comm_right φ) (autoToFitting_induces φ)

/-- A compatible filling of the identity cube is local on stalks. -/
private theorem fittingToAuto_isLocal {L : FlatLift t f}
    (φ : Solution.Fitting (toSolution L) (toSolution L)) :
    ∀ x : L.space, IsLocalHom ((@FittingMap.hom _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance _ φ).hom.stalkMap x).hom := sorry

/-- The scheme morphism underlying a compatible filling is over the base. -/
private theorem fittingToAuto_over {L : FlatLift t f}
    (φ : Solution.Fitting (toSolution L) (toSolution L)) :
    (⟨LocallyRingedSpace.homMk (@FittingMap.hom _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance _ φ) (fittingToAuto_isLocal φ)⟩ : L.space ⟶ L.space) ≫
      L.f' = L.f' := sorry

/-- The scheme morphism underlying a compatible filling fixes the closed fibre. -/
private theorem fittingToAuto_restrict {L : FlatLift t f}
    (φ : Solution.Fitting (toSolution L) (toSolution L)) :
    L.i ≫ (⟨LocallyRingedSpace.homMk (@FittingMap.hom _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance _ φ) (fittingToAuto_isLocal φ)⟩ : L.space ⟶ L.space) =
      L.i := sorry

/-- The scheme morphism underlying a compatible filling is invertible. -/
private theorem fittingToAuto_isIso {L : FlatLift t f}
    (φ : Solution.Fitting (toSolution L) (toSolution L)) :
    @IsIso Scheme _ L.space L.space (⟨LocallyRingedSpace.homMk (@FittingMap.hom _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance _ φ) (fittingToAuto_isLocal φ)⟩ : L.space ⟶ L.space) := sorry

/-- Rebuild a reducing-to-identity automorphism from its compatible filling. -/
private def fittingToAuto {L : FlatLift t f}
    (φ : Solution.Fitting (toSolution L) (toSolution L)) : ReduceIdAuto L where
  hom := ⟨LocallyRingedSpace.homMk (@FittingMap.hom _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance _ φ) (fittingToAuto_isLocal φ)⟩
  over := fittingToAuto_over φ
  restrict := fittingToAuto_restrict φ
  isIso := fittingToAuto_isIso φ

/-- Maps `Ω[f] ⟶ i_* 𝒢` for the identity connecting cube of a flat lift. -/
abbrev homOmega (L : FlatLift t f) :=
  Ω[f.toShHom] ⟶
    (RingedSpace.Hom.pushforward (𝟙 X.toRingedSpace)).obj
      (RingedSpace.Hom.idealModule L.i.toShHom)

/-- The Ext⁰ class associated to a map `Ω[f] ⟶ i_* 𝒢`, transported along
`L(𝟙 X)^* ≅ id` and `Ker(i^♯) ≅ f^* 𝒞_{S/S'}`. -/
@[no_expose] def homOmegaToExtZero {L : FlatLift t f} (α : homOmega L) : extZeroNL t f :=
  (AlgebraicGeometry.RingedSpace.modulePullbackDerived.idIso X.toRingedSpace).inv.app
      ((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[f.toShHom]) ≫
    homOmegaExtZero α ≫
      (shiftFunctor (DerivedCategory X.toRingedSpace.Modules) (0 : ℤ)).map
        ((DerivedCategory.Q (C := X.toRingedSpace.Modules)).map
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map (kernelIso L).hom))

/-- Undo the `kernelIso` identification on an Ext⁰ class. -/
private def extZeroUnkernel (L : FlatLift t f) (ξ : extZeroNL t f) :
    Ext⁽(0 : ℤ)⁾((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[f.toShHom],
      (DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj
        ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
          (RingedSpace.Hom.idealModule L.i.toShHom))) :=
  ξ ≫ (shiftFunctor (DerivedCategory X.toRingedSpace.Modules) (0 : ℤ)).map
    ((DerivedCategory.Q (C := X.toRingedSpace.Modules)).map
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map (kernelIso L).inv))

/-- `extZeroUnkernel` postcomposes with the inverse kernel identification. -/
private theorem extZeroUnkernel_apply (L : FlatLift t f) (ξ : extZeroNL t f) :
    extZeroUnkernel L ξ =
      ξ ≫ (shiftFunctor (DerivedCategory X.toRingedSpace.Modules) (0 : ℤ)).map
        ((DerivedCategory.Q (C := X.toRingedSpace.Modules)).map
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map
            (kernelIso L).inv)) := by rfl

/-- Ext⁰ of `L(𝟙 X)^* NL[f]` against `Ker(i^♯)[0]`, the group of `homOmegaExtZero`. -/
private abbrev homOmegaExtZeroType (L : FlatLift t f) :=
  Ext⁽(0 : ℤ)⁾((AlgebraicGeometry.RingedSpace.modulePullbackDerived
      (𝟙 X.toRingedSpace)).obj ((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[f.toShHom]),
    (DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
        (RingedSpace.Hom.idealModule L.i.toShHom)))

/-- Undo `idIso` and `kernelIso` so the class lies in the domain of
`homOmegaExtZero`. -/
private def extZeroUntransport (L : FlatLift t f) (ξ : extZeroNL t f) :
    homOmegaExtZeroType L :=
  (AlgebraicGeometry.RingedSpace.modulePullbackDerived.idIso X.toRingedSpace).hom.app
      ((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[f.toShHom]) ≫ extZeroUnkernel L ξ

/-- `extZeroUntransport` is `idIso.hom` precomposed with `extZeroUnkernel`. -/
private theorem extZeroUntransport_apply (L : FlatLift t f) (ξ : extZeroNL t f) :
    extZeroUntransport L ξ =
      (AlgebraicGeometry.RingedSpace.modulePullbackDerived.idIso X.toRingedSpace).hom.app
          ((DerivedCategory.Q (C := X.toRingedSpace.Modules)).obj NL[f.toShHom]) ≫ extZeroUnkernel L ξ := by rfl

/-- Recover a map `Ω[f] ⟶ i_* 𝒢` from an Ext⁰ class by inverting the
`idIso` / `homOmegaExtZero` / `kernelIso` chain. -/
@[no_expose] def extZeroToHomOmega (L : FlatLift t f) (ξ : extZeroNL t f) : homOmega L :=
  (@homOmegaExtZeroAddEquiv _ _ _ _ L.i.toShHom f.toShHom
    (𝟙 X.toRingedSpace) (toSolution L).i_isFirstOrder).symm (extZeroUntransport L ξ)

/-- `extZeroToHomOmega` inverts `homOmegaToExtZero`. -/
theorem extZeroToHomOmega_left_inv {L : FlatLift t f} (α : homOmega L) :
    extZeroToHomOmega L (homOmegaToExtZero α) = α := sorry

/-- `homOmegaToExtZero` inverts `extZeroToHomOmega`. -/
theorem extZeroToHomOmega_right_inv (L : FlatLift t f) (ξ : extZeroNL t f) :
    homOmegaToExtZero (extZeroToHomOmega L ξ) = ξ := sorry

/-- The unique map `Ω[f] ⟶ i_* 𝒢` comparing a reducing-to-identity automorphism
with the identity filling of the identity cube. -/
@[no_expose] def derivationOfAuto {L : FlatLift t f} (φ : ReduceIdAuto L) : homOmega L :=
  @FittingMap.diff _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance (Solution.compare (toSolution L) (toSolution L))
    (idFitting L) (autoToFitting φ)

-- Local declaration justification (module visibility): this dependent public construction
-- needs its private implementation certificates available during elaboration.
set_option backward.privateInPublic true in
/-- `derivationOfAuto φ` is the unique perturbation sending the identity filling
to the filling of `φ`. -/
theorem derivationOfAuto_spec {L : FlatLift t f} (φ : ReduceIdAuto L) :
    @FittingMap.perturb _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance (Solution.compare (toSolution L) (toSolution L))
    (derivationOfAuto φ) (idFitting L) = autoToFitting φ := sorry

/-- The Ext⁰ class of a reducing-to-identity automorphism, via the identity-cube
perturbation and the Hom(Ω, f^* 𝒞) ↔ Ext⁰ transport. -/
@[no_expose] def toExtZero {L : FlatLift t f} (φ : ReduceIdAuto L) : extZeroNL t f :=
  homOmegaToExtZero (derivationOfAuto φ)

/-- `toExtZero` is `homOmegaToExtZero` of the identity-cube derivation. -/
theorem toExtZero_apply {L : FlatLift t f} (φ : ReduceIdAuto L) :
    toExtZero φ = homOmegaToExtZero (derivationOfAuto φ) := by rfl

/-- The Ext⁰-action on reducing-to-identity automorphisms, via identity-cube
perturbation. -/
@[no_expose] def ofExtZero (L : FlatLift t f) (ξ : extZeroNL t f) : ReduceIdAuto L :=
  fittingToAuto (@FittingMap.perturb _ _ _ _ _ _ _ _
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (toSolution L).i f.toShHom (toSolution L).f' t.toShHom
      (𝟙 X.toRingedSpace) (𝟙 S.toRingedSpace) (𝟙 S'.toRingedSpace)
      (toSolution L).i_isFirstOrder inferInstance (toSolution L).i_isFirstOrder inferInstance (Solution.compare (toSolution L) (toSolution L))
    (extZeroToHomOmega L ξ) (idFitting L))

/-- The identity automorphism is the image of the zero Ext⁰ class. -/
theorem ofExtZero_zero (L : FlatLift t f) :
    ofExtZero L 0 = ReduceIdAuto.id L := sorry

/-- Translation by a fixed flat lift identifies Ext¹ with lift isomorphism classes. -/
def isoClassEquiv (S0 : FlatLift t f) : extOneNL t f ≃ IsoClass t f :=
  @Equiv.vaddConst (extOneNL t f) (IsoClass t f) _ (addTorsor S0) (isoClassMk S0)

/-- The based chart sends an Ext¹ class ξ to the translate of the basepoint. -/
theorem isoClassEquiv_apply (S0 : FlatLift t f) (ξ : extOneNL t f) :
    isoClassEquiv S0 ξ = ξ +ᵥ isoClassMk S0 := by rfl

/-- The zero Ext¹ class is sent to the class of the basepoint. -/
theorem isoClassEquiv_zero (S0 : FlatLift t f) :
    isoClassEquiv S0 0 = isoClassMk S0 := sorry

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (S0 : FlatLift t f) (p : IsoClass t f) :
    (isoClassEquiv S0).symm p = p -ᵥ isoClassMk S0 := by rfl

/-- The canonical Ext⁰ construction recovers each reducing automorphism. -/
private theorem reduceIdAutoEquiv_left_inv (L : FlatLift t f) :
    Function.LeftInverse (ofExtZero L) (fun φ : ReduceIdAuto L ↦ toExtZero φ) := sorry

/-- Reducing automorphisms realize each Ext⁰ class. -/
private theorem reduceIdAutoEquiv_right_inv (L : FlatLift t f) :
    Function.RightInverse (ofExtZero L) (fun φ : ReduceIdAuto L ↦ toExtZero φ) := sorry

/-- Automorphisms of a flat lift fixing the closed fibre are classified by Ext⁰. -/
@[no_expose] def reduceIdAutoEquiv (L : FlatLift t f) : ReduceIdAuto L ≃ extZeroNL t f where
  toFun φ := toExtZero φ
  invFun ξ := ofExtZero L ξ
  left_inv := reduceIdAutoEquiv_left_inv L
  right_inv := reduceIdAutoEquiv_right_inv L

/-- The forward chart sends a reducing-to-identity automorphism to its Ext⁰ class. -/
theorem reduceIdAutoEquiv_apply (L : FlatLift t f) (φ : ReduceIdAuto L) :
    reduceIdAutoEquiv L φ = toExtZero φ := by rfl

/-- The inverse chart sends an Ext⁰ class to the identity-cube perturbation of
the identity automorphism. -/
theorem reduceIdAutoEquiv_symm_apply (L : FlatLift t f) (ξ : extZeroNL t f) :
    (reduceIdAutoEquiv L).symm ξ = ofExtZero L ξ := by rfl

/-- The identity automorphism is sent to the zero Ext⁰ class. -/
theorem reduceIdAutoEquiv_zero (L : FlatLift t f) :
    reduceIdAutoEquiv L (ReduceIdAuto.id L) = 0 := sorry

end FlatLift
end AlgebraicGeometry.Scheme.Thickening
