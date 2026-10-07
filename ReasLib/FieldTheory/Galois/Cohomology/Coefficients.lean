module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.RingTheory.RootsOfUnity.Action
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

open CategoryTheory CategoryTheory.Action ModuleCat

universe u

noncomputable section

namespace GaloisCohomology

variable (K Ksep : Type u) [Field K] [Field Ksep]
  [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The trivial Galois action on the lifted group `ZMod n` has open stabilizers. -/
theorem constantZModModule_openStabilizer (n : ℕ) :
    openStabilizer ℤ (Gal(Ksep / K))
      (Action.trivial (Gal(Ksep / K)) (ModuleCat.of ℤ (ULift.{u} (ZMod n)))) := sorry

/-- The discrete Galois module on the lifted group `ZMod n` with trivial action. -/
def constantZModModule (n : ℕ) : DiscreteModuleCat ℤ (Gal(Ksep / K)) :=
  ⟨Action.trivial (Gal(Ksep / K)) (ModuleCat.of ℤ (ULift.{u} (ZMod n))),
    constantZModModule_openStabilizer K Ksep n⟩

/-- The underlying integral module of the constant Galois module is the lifted `ZMod n`. -/
theorem constantZModModule_obj (n : ℕ) :
    (constantZModModule K Ksep n).obj.V = ModuleCat.of ℤ (ULift.{u} (ZMod n)) := sorry

/-- Every Galois element acts trivially on the constant Galois module. -/
theorem constantZModModule_action (n : ℕ) (sigma : Gal(Ksep / K)) :
    (constantZModModule K Ksep n).obj.ρ sigma = 𝟙 _ := sorry

/-- The identity Galois automorphism acts identically on the additive separable closure. -/
theorem additiveAction_map_one :
    ModuleCat.ofHom
      (1 : Gal(Ksep / K)).toRingHom.toAddMonoidHom.toIntLinearMap =
        (1 : End (ModuleCat.of ℤ Ksep)) := sorry

/-- Composition of Galois automorphisms agrees with composition of their additive maps. -/
theorem additiveAction_map_mul (sigma tau : Gal(Ksep / K)) :
    ModuleCat.ofHom (sigma * tau).toRingHom.toAddMonoidHom.toIntLinearMap =
      ModuleCat.ofHom tau.toRingHom.toAddMonoidHom.toIntLinearMap ≫
        ModuleCat.ofHom sigma.toRingHom.toAddMonoidHom.toIntLinearMap := sorry

/-- The natural Galois action on the additive separable closure has open stabilizers. -/
theorem additiveAction_openStabilizer :
    openStabilizer ℤ (Gal(Ksep / K))
      { V := ModuleCat.of ℤ Ksep
        ρ := { toFun := fun sigma ↦
                 ModuleCat.ofHom sigma.toRingHom.toAddMonoidHom.toIntLinearMap
               map_one' := additiveAction_map_one K Ksep
               map_mul' := additiveAction_map_mul K Ksep } } := sorry

/-- The discrete integral Galois module on the additive separable closure. -/
def additiveModule : DiscreteModuleCat ℤ (Gal(Ksep / K)) :=
  ⟨{ V := ModuleCat.of ℤ Ksep
     ρ := { toFun := fun sigma ↦
              ModuleCat.ofHom sigma.toRingHom.toAddMonoidHom.toIntLinearMap
            map_one' := additiveAction_map_one K Ksep
            map_mul' := additiveAction_map_mul K Ksep } },
    additiveAction_openStabilizer K Ksep⟩

/-- The underlying integral module of the additive Galois module is `Ksep`. -/
theorem additiveModule_obj :
    (additiveModule K Ksep).obj.V = ModuleCat.of ℤ Ksep := sorry

/-- The additive Galois module acts by the additive maps of field automorphisms. -/
theorem additiveModule_action (sigma : Gal(Ksep / K)) :
    (additiveModule K Ksep).obj.ρ sigma =
      ModuleCat.ofHom sigma.toRingHom.toAddMonoidHom.toIntLinearMap := sorry

/-- The identity Galois automorphism acts identically on roots of unity. -/
theorem rootsOfUnityAction_map_one (n : ℕ) :
    ModuleCat.ofHom
      ((MulAut.restrictRootsOfUnityHom n
        (RingAut.toMulAut Ksep (1 : Gal(Ksep / K)).toRingEquiv)).toMonoidHom.toAdditive.toIntLinearMap) =
      (1 : End (ModuleCat.of ℤ (Additive (rootsOfUnity n Ksep)))) := sorry

/-- Composition of Galois automorphisms agrees with their induced maps on roots of unity. -/
theorem rootsOfUnityAction_map_mul (n : ℕ) (sigma tau : Gal(Ksep / K)) :
    ModuleCat.ofHom
      ((MulAut.restrictRootsOfUnityHom n
        (RingAut.toMulAut Ksep (sigma * tau).toRingEquiv)).toMonoidHom.toAdditive.toIntLinearMap) =
      ModuleCat.ofHom
        ((MulAut.restrictRootsOfUnityHom n
          (RingAut.toMulAut Ksep tau.toRingEquiv)).toMonoidHom.toAdditive.toIntLinearMap) ≫
      ModuleCat.ofHom
        ((MulAut.restrictRootsOfUnityHom n
          (RingAut.toMulAut Ksep sigma.toRingEquiv)).toMonoidHom.toAdditive.toIntLinearMap) := sorry

/-- The natural Galois action on roots of unity has open stabilizers. -/
theorem rootsOfUnityAction_openStabilizer (n : ℕ) :
    openStabilizer ℤ (Gal(Ksep / K))
      { V := ModuleCat.of ℤ (Additive (rootsOfUnity n Ksep))
        ρ := { toFun := fun sigma ↦ ModuleCat.ofHom
                 ((MulAut.restrictRootsOfUnityHom n
                   (RingAut.toMulAut Ksep sigma.toRingEquiv)).toMonoidHom.toAdditive.toIntLinearMap)
               map_one' := rootsOfUnityAction_map_one K Ksep n
               map_mul' := rootsOfUnityAction_map_mul K Ksep n } } := sorry

/-- The discrete integral Galois module on the additive presentation of roots of unity. -/
def rootsOfUnityModule (n : ℕ) : DiscreteModuleCat ℤ (Gal(Ksep / K)) :=
  ⟨{ V := ModuleCat.of ℤ (Additive (rootsOfUnity n Ksep))
     ρ := { toFun := fun sigma ↦ ModuleCat.ofHom
              ((MulAut.restrictRootsOfUnityHom n
                (RingAut.toMulAut Ksep sigma.toRingEquiv)).toMonoidHom.toAdditive.toIntLinearMap)
            map_one' := rootsOfUnityAction_map_one K Ksep n
            map_mul' := rootsOfUnityAction_map_mul K Ksep n } },
    rootsOfUnityAction_openStabilizer K Ksep n⟩

/-- The underlying module of the roots-of-unity Galois module is its additive presentation. -/
theorem rootsOfUnityModule_obj (n : ℕ) :
    (rootsOfUnityModule K Ksep n).obj.V =
      ModuleCat.of ℤ (Additive (rootsOfUnity n Ksep)) := sorry

/-- The Galois action on roots of unity is restriction of field automorphisms. -/
theorem rootsOfUnityModule_action (n : ℕ) (sigma : Gal(Ksep / K)) :
    (rootsOfUnityModule K Ksep n).obj.ρ sigma = ModuleCat.ofHom
      ((MulAut.restrictRootsOfUnityHom n
        (RingAut.toMulAut Ksep sigma.toRingEquiv)).toMonoidHom.toAdditive.toIntLinearMap) := sorry

end GaloisCohomology

end
