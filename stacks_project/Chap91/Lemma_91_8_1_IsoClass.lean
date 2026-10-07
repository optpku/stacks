module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import stacks_project.Chap91.Lemma_91_8_1_Translate
public import stacks_project.Chap91.Lemma_91_7_3_IsoClass

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
open AlgebraicGeometry.RingedSpace.Thickening (moduleQ FittingMap homOmegaExtZero Solution)
open scoped AlgebraicGeometry DerivedExt RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Thickening
namespace FlatLift

variable {S S' X : Scheme.{u}}
variable {t : S ⟶ S'} [IsFirstOrderThickening t] {f : X ⟶ S} [Flat f]

/-- The setoid identifying flat lifts that admit an ambient isomorphism over `S'`
reducing to the identity on `X`. -/
def isoSetoid (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) [Flat f] :
    Setoid (FlatLift t f) where
  r L₁ L₂ := Nonempty (Hom L₁ L₂)
  iseqv := sorry

/-- Two flat lifts are related iff they admit a morphism of lifts. -/
theorem isoSetoid_rel (L₁ L₂ : FlatLift t f) :
    isoSetoid t f L₁ L₂ ↔ Nonempty (Hom L₁ L₂) := sorry

/-- Isomorphism classes of flat first-order lifts of `f` across `t`. -/
abbrev IsoClass (t : S ⟶ S') [IsFirstOrderThickening t] (f : X ⟶ S) [Flat f] :=
  Quotient (isoSetoid t f)

/-- The isomorphism class of a given flat lift. -/
def isoClassMk (L : FlatLift t f) : IsoClass t f :=
  Quotient.mk (isoSetoid t f) L

/-- A morphism of flat lifts identifies isomorphism classes. -/
theorem isoClassMk_eq_mk_of_hom {L₁ L₂ : FlatLift t f} (φ : Hom L₁ L₂) :
    isoClassMk L₁ = isoClassMk L₂ := sorry

/-- The obstruction class in Ext¹(NL[f], f^* 𝒞_{S/S'}) comparing two flat lifts,
transported from the identity-cube obstruction of the associated 91.7.0.1
solutions. -/
def obstruction (L₁ L₂ : FlatLift t f) : extOneNL t f :=
  Solution.obstruction (toSolution L₁) (toSolution L₂)

/-- `obstruction` is the ringed-space identity-cube obstruction of `toSolution`. -/
theorem obstruction_spec (L₁ L₂ : FlatLift t f) :
    obstruction L₁ L₂ = Solution.obstruction (toSolution L₁) (toSolution L₂) := sorry

/-- The obstruction vanishes iff the two lifts admit a morphism of lifts. -/
theorem obstruction_eq_zero_iff (L₁ L₂ : FlatLift t f) :
    obstruction L₁ L₂ = 0 ↔ Nonempty (Hom L₁ L₂) := sorry

/-- Translating a lift by ξ realizes ξ as an obstruction. -/
theorem obstruction_translate (ξ : extOneNL t f) (L : FlatLift t f) :
    obstruction L (translate ξ L) = ξ := sorry

/-- Action of an Ext¹ class on an isomorphism class, via `translate`. -/
def vadd (ξ : extOneNL t f) (p : IsoClass t f) : IsoClass t f :=
  Quotient.map (translate ξ) sorry p

/-- Difference of isomorphism classes, as an Ext¹ class. Subtraction is oriented
so that `[X'_ξ] -ᵥ [X'] = ξ` when `o(X', X'_ξ) = ξ`. -/
def vsub (p q : IsoClass t f) : extOneNL t f :=
  Quotient.lift₂ (fun L₁ L₂ ↦ obstruction L₂ L₁) sorry p q

/-- Ext¹ classes act on isomorphism classes of flat lifts by translation. -/
instance instVAdd_isoClass : VAdd (extOneNL t f) (IsoClass t f) where
  vadd := vadd

/-- Difference of isomorphism classes of flat lifts is an Ext¹ class. -/
instance instVSub_isoClass : VSub (extOneNL t f) (IsoClass t f) where
  vsub := vsub

/-- The Ext¹-action of naive cotangent classes on isomorphism classes of flat
lifts. -/
instance instAddAction_isoClass : AddAction (extOneNL t f) (IsoClass t f) where
  add_vadd := sorry
  zero_vadd := sorry

/-- The Ext¹-action computes on representatives by `translate`. -/
theorem vadd_mk (ξ : extOneNL t f) (L : FlatLift t f) :
    ξ +ᵥ isoClassMk L = isoClassMk (translate ξ L) := sorry

/-- Torsor subtraction computes on representatives by the reversed obstruction. -/
theorem vsub_mk (L₁ L₂ : FlatLift t f) :
    isoClassMk L₁ -ᵥ isoClassMk L₂ = obstruction L₂ L₁ := sorry

/-- The zero Ext¹ class acts as the identity on isomorphism classes. -/
theorem vadd_zero (p : IsoClass t f) :
    (0 : extOneNL t f) +ᵥ p = p := sorry

/-- The Ext¹-action is compatible with addition. -/
theorem add_vadd (ξ η : extOneNL t f) (p : IsoClass t f) :
    (ξ + η) +ᵥ p = ξ +ᵥ η +ᵥ p := sorry

/-- With a chosen flat lift as basepoint, isomorphism classes are an additive
torsor under Ext¹(NL[f], f^* 𝒞_{S/S'}). -/
@[reducible]
def addTorsor (S0 : FlatLift t f) : AddTorsor (extOneNL t f) (IsoClass t f) where
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := sorry
  vadd_vsub' := sorry

/-- A basepoint lift makes the set of isomorphism classes nonempty. -/
theorem addTorsor_nonempty (S0 : FlatLift t f) : Nonempty (IsoClass t f) :=
  (addTorsor S0).nonempty

/-- The identity connecting cube of the associated 91.7.0.1 solutions of a flat
lift. -/
def idCube (L : FlatLift t f) :=
  Solution.compare (toSolution L) (toSolution L)

/-- The identity filling of the identity cube of a flat lift. -/
def idFitting (L : FlatLift t f) : FittingMap (idCube L) :=
  FittingMap.of (𝟙 (toSolution L).space) sorry sorry sorry

/-- Convert a reducing-to-identity automorphism into a filling of the identity
cube. -/
def autoToFitting {L : FlatLift t f} (φ : ReduceIdAuto L) : FittingMap (idCube L) :=
  FittingMap.of φ.hom.toShHom sorry sorry sorry

/-- Rebuild a reducing-to-identity automorphism from a filling of the identity
cube. -/
def fittingToAuto {L : FlatLift t f} (φ : FittingMap (idCube L)) : ReduceIdAuto L where
  hom := ⟨LocallyRingedSpace.homMk φ.hom sorry⟩
  over := sorry
  restrict := sorry
  isIso := sorry

/-- Maps `Ω[f] ⟶ i_* 𝒢` for the identity connecting cube of a flat lift. -/
abbrev homOmega (L : FlatLift t f) :=
  Ω[f.toShHom] ⟶
    (RingedSpace.Hom.pushforward (𝟙 X.toRingedSpace)).obj
      (RingedSpace.Hom.idealModule L.i.toShHom)

/-- The Ext⁰ class associated to a map `Ω[f] ⟶ i_* 𝒢`, transported along
`L(𝟙 X)^* ≅ id` and `Ker(i^♯) ≅ f^* 𝒞_{S/S'}`. -/
def homOmegaToExtZero {L : FlatLift t f} (α : homOmega L) : extZeroNL t f :=
  (AlgebraicGeometry.RingedSpace.modulePullbackDerived.idIso X.toRingedSpace).inv.app
      ((moduleQ X.toRingedSpace).obj NL[f.toShHom]) ≫
    homOmegaExtZero α ≫
      (shiftFunctor (DerivedCategory X.toRingedSpace.Modules) (0 : ℤ)).map
        ((moduleQ X.toRingedSpace).map
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map (kernelIso L).hom))

/-- Undo the `kernelIso` identification on an Ext⁰ class. -/
def extZeroUnkernel (L : FlatLift t f) (ξ : extZeroNL t f) :
    Ext⁽(0 : ℤ)⁾((moduleQ X.toRingedSpace).obj NL[f.toShHom],
      (moduleQ X.toRingedSpace).obj
        ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
          (RingedSpace.Hom.idealModule L.i.toShHom))) :=
  ξ ≫ (shiftFunctor (DerivedCategory X.toRingedSpace.Modules) (0 : ℤ)).map
    ((moduleQ X.toRingedSpace).map
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map (kernelIso L).inv))

/-- `extZeroUnkernel` postcomposes with the inverse kernel identification. -/
theorem extZeroUnkernel_apply (L : FlatLift t f) (ξ : extZeroNL t f) :
    extZeroUnkernel L ξ =
      ξ ≫ (shiftFunctor (DerivedCategory X.toRingedSpace.Modules) (0 : ℤ)).map
        ((moduleQ X.toRingedSpace).map
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).map
            (kernelIso L).inv)) := sorry

/-- Ext⁰ of `L(𝟙 X)^* NL[f]` against `Ker(i^♯)[0]`, the group of `homOmegaExtZero`. -/
abbrev homOmegaExtZeroType (L : FlatLift t f) :=
  Ext⁽(0 : ℤ)⁾((AlgebraicGeometry.RingedSpace.modulePullbackDerived
      (𝟙 X.toRingedSpace)).obj ((moduleQ X.toRingedSpace).obj NL[f.toShHom]),
    (moduleQ X.toRingedSpace).obj
      ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
        (RingedSpace.Hom.idealModule L.i.toShHom)))

/-- `homOmegaExtZeroType` is Ext⁰ of derived pullback of `NL[f]` against the kernel. -/
theorem homOmegaExtZeroType_eq (L : FlatLift t f) :
    homOmegaExtZeroType L =
      Ext⁽(0 : ℤ)⁾((AlgebraicGeometry.RingedSpace.modulePullbackDerived
          (𝟙 X.toRingedSpace)).obj ((moduleQ X.toRingedSpace).obj NL[f.toShHom]),
        (moduleQ X.toRingedSpace).obj
          ((CochainComplex.singleFunctor X.toRingedSpace.Modules 0).obj
            (RingedSpace.Hom.idealModule L.i.toShHom))) := sorry

/-- Undo `idIso` and `kernelIso` so the class lies in the domain of
`homOmegaExtZero`. -/
def extZeroUntransport (L : FlatLift t f) (ξ : extZeroNL t f) :
    homOmegaExtZeroType L :=
  (AlgebraicGeometry.RingedSpace.modulePullbackDerived.idIso X.toRingedSpace).hom.app
      ((moduleQ X.toRingedSpace).obj NL[f.toShHom]) ≫ extZeroUnkernel L ξ

/-- `extZeroUntransport` is `idIso.hom` precomposed with `extZeroUnkernel`. -/
theorem extZeroUntransport_apply (L : FlatLift t f) (ξ : extZeroNL t f) :
    extZeroUntransport L ξ =
      (AlgebraicGeometry.RingedSpace.modulePullbackDerived.idIso X.toRingedSpace).hom.app
          ((moduleQ X.toRingedSpace).obj NL[f.toShHom]) ≫ extZeroUnkernel L ξ := sorry

/-- Inverse of `homOmegaExtZero`: unshift by `ShiftedHom.homEquiv`, undo `idIso`,
pass to `H⁰`, and identify `H⁰(NL[f]) ≅ Ω[f]` with the identity adjunction. -/
def homOmegaExtZeroInv {L : FlatLift t f} (ξ : homOmegaExtZeroType L) :
    homOmega L :=
  (RingedSpace.Hom.pullbackPushforwardAdjunction (𝟙 X.toRingedSpace)).homEquiv
      Ω[f.toShHom] (RingedSpace.Hom.idealModule L.i.toShHom)
    ((RingedSpace.Hom.pullbackIdIso X.toRingedSpace).hom.app Ω[f.toShHom] ≫
      (RingedSpace.NaiveCotangent.homologyZeroIso f.toShHom).inv ≫
        (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (0 : ℤ)).inv.app
          NL[f.toShHom] ≫
        (DerivedCategory.homologyFunctor X.toRingedSpace.Modules (0 : ℤ)).map
          ((AlgebraicGeometry.RingedSpace.modulePullbackDerived.idIso
              X.toRingedSpace).inv.app
              ((moduleQ X.toRingedSpace).obj NL[f.toShHom]) ≫
            (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl).symm ξ) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
            X.toRingedSpace.Modules (0 : ℤ)).hom.app
          (RingedSpace.Hom.idealModule L.i.toShHom))

/-- `homOmegaExtZeroInv` inverts `homOmegaExtZero`. -/
theorem homOmegaExtZeroInv_left_inv {L : FlatLift t f} (α : homOmega L) :
    homOmegaExtZeroInv (homOmegaExtZero α) = α := sorry

/-- `homOmegaExtZero` inverts `homOmegaExtZeroInv`. -/
theorem homOmegaExtZeroInv_right_inv {L : FlatLift t f} (ξ : homOmegaExtZeroType L) :
    homOmegaExtZero (homOmegaExtZeroInv ξ) = ξ := sorry

/-- Recover a map `Ω[f] ⟶ i_* 𝒢` from an Ext⁰ class by inverting the
`idIso` / `homOmegaExtZero` / `kernelIso` chain. -/
def extZeroToHomOmega (L : FlatLift t f) (ξ : extZeroNL t f) : homOmega L :=
  homOmegaExtZeroInv (extZeroUntransport L ξ)

/-- `extZeroToHomOmega` inverts `homOmegaToExtZero`. -/
theorem extZeroToHomOmega_left_inv {L : FlatLift t f} (α : homOmega L) :
    extZeroToHomOmega L (homOmegaToExtZero α) = α := sorry

/-- `homOmegaToExtZero` inverts `extZeroToHomOmega`. -/
theorem extZeroToHomOmega_right_inv (L : FlatLift t f) (ξ : extZeroNL t f) :
    homOmegaToExtZero (extZeroToHomOmega L ξ) = ξ := sorry

/-- The unique map `Ω[f] ⟶ i_* 𝒢` comparing a reducing-to-identity automorphism
with the identity filling of the identity cube. -/
def derivationOfAuto {L : FlatLift t f} (φ : ReduceIdAuto L) : homOmega L :=
  FittingMap.diff (idFitting L) (autoToFitting φ)

/-- `derivationOfAuto φ` is the unique perturbation sending the identity filling
to the filling of `φ`. -/
theorem derivationOfAuto_spec {L : FlatLift t f} (φ : ReduceIdAuto L) :
    FittingMap.perturb (derivationOfAuto φ) (idFitting L) = autoToFitting φ := sorry

/-- The Ext⁰ class of a reducing-to-identity automorphism, via the identity-cube
perturbation of lemma 91.7.1 (2) and the Hom(Ω, f^* 𝒞) ↔ Ext⁰ transport. -/
def toExtZero {L : FlatLift t f} (φ : ReduceIdAuto L) : extZeroNL t f :=
  homOmegaToExtZero (derivationOfAuto φ)

/-- `toExtZero` is `homOmegaToExtZero` of the identity-cube derivation. -/
theorem toExtZero_apply {L : FlatLift t f} (φ : ReduceIdAuto L) :
    toExtZero φ = homOmegaToExtZero (derivationOfAuto φ) := sorry

/-- The Ext⁰-action on reducing-to-identity automorphisms, via identity-cube
perturbation. -/
def ofExtZero (L : FlatLift t f) (ξ : extZeroNL t f) : ReduceIdAuto L :=
  fittingToAuto (FittingMap.perturb (extZeroToHomOmega L ξ) (idFitting L))

/-- The identity automorphism is the image of the zero Ext⁰ class. -/
theorem ofExtZero_zero (L : FlatLift t f) :
    ofExtZero L 0 = ReduceIdAuto.id L := sorry

end FlatLift
end AlgebraicGeometry.Scheme.Thickening
