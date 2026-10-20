module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SquareZeroLift
public import Mathlib.Algebra.Torsor.Defs

/-!
# Isomorphism classes of square-zero lifts of derived modules

Comparison obstructions give based charts and the canonical additive torsor structure on
isomorphism classes of bounded-above lifts.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open SheafOfModules.RingedSite
open scoped CategoryTheory.DerivedCategory.DerivedTensor
open scoped DerivedExt

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, `DerivedTensor.Right.functor`, and `moduleDerivedAdjunction` must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): `monoidalCategory` is reducible to `KFlat.monoidalCategory` at the pinned `moduleCat_hasDerivedCategory`; `ρ_`, whiskering, `tensorLeft`, `mapUnitIso`, and the Ext target of `mapObstruction` must share that tensor.
attribute [local instance] monoidalCategory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]

variable {𝒪 𝒪₀ : Sheaf J CommRingCat.{w}} (π : 𝒪 ⟶ 𝒪₀)
variable [Sheaf.IsLocallySurjective π]
variable (h_sq : KernelIdeal.IsSquareZero π)
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))) (up ℤ)]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) (up ℤ)]
variable [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{w} (sameSiteHom π))
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [DerivedAdjunction.HasPair.{w} (sameSiteHom π)]
variable [KFlat.HomotopyTensorDescends 𝒪]
variable [KFlat.TensorDescends 𝒪]
variable [KFlat.IsLocalization 𝒪]
variable [KFlat.HomotopyTensorDescends 𝒪₀]
variable [KFlat.TensorDescends 𝒪₀]
variable [KFlat.IsLocalization 𝒪₀]
variable [Tensor.Has 𝒪₀]
variable [(tensorO0 π).OplaxMonoidal]
variable [(pushforwardO0 π).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)), (tensorLeft L).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (M : ModuleDerived.{w, u, v, w}
      (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)),
  IsIso ((moduleDerivedAdjunction.{w} (sameSiteHom π)).projectionFormulaMate L M)]
variable [IsIso (pushforwardSingleUnit π (unitModule J 𝒪₀))]

variable (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))

/-- Two lifts are equivalent when there is an isomorphism of pairs. -/
def isoSetoid : Setoid (Lift π h_sq K₀) where
  r L₁ L₂ := Nonempty (LiftIso π h_sq L₁ L₂)
  iseqv := sorry

/-- Isomorphism classes of lifts of `K₀` along `π`. -/
abbrev IsoClass := Quotient (isoSetoid π h_sq K₀)

namespace IsoClass

/-- The isomorphism class of a given lift. -/
def mk (L : Lift π h_sq K₀) : IsoClass π h_sq K₀ :=
  Quotient.mk (isoSetoid π h_sq K₀) L

/-- An isomorphism of lifts identifies their isomorphism classes. -/
theorem mk_eq_mk_of_iso {L₁ L₂ : Lift π h_sq K₀} (φ : LiftIso π h_sq L₁ L₂) :
    mk π h_sq K₀ L₁ = mk π h_sq K₀ L₂ := sorry

end IsoClass

/-- The obstruction class of a comparison map of lifts, transported to
`Ext⁽1⁾(K₀, K₀ ⊗ ℐ[0])`. -/
noncomputable def obstruction (L L' : Lift π h_sq K₀) :
    Ext⁽(1 : ℤ)⁾(K₀, K₀ ⊗ kernelIdeal0Single π h_sq) :=
  L.iso.inv ≫ mapObstruction π h_sq (L.iso.hom ≫ L'.iso.inv) ≫
    ((L'.iso.hom ▷ kernelIdeal0Single π h_sq)⟦(1 : ℤ)⟧')

/-- `obstruction` is the transport of `mapObstruction` of `L.iso.hom ≫ L'.iso.inv`. -/
theorem obstruction_mk (L L' : Lift π h_sq K₀) :
    obstruction π h_sq K₀ L L' =
      L.iso.inv ≫ mapObstruction π h_sq (L.iso.hom ≫ L'.iso.inv) ≫
        ((L'.iso.hom ▷ kernelIdeal0Single π h_sq)⟦(1 : ℤ)⟧') := sorry

/-- The obstruction of a lift against itself vanishes. -/
theorem obstruction_self (L : Lift π h_sq K₀) :
    obstruction π h_sq K₀ L L = 0 := sorry

/-- Obstruction classes of lifts satisfy the cocycle relation. -/
theorem obstruction_comp (L₁ L₂ L₃ : Lift π h_sq K₀) :
    obstruction π h_sq K₀ L₁ L₃ =
      obstruction π h_sq K₀ L₁ L₂ + obstruction π h_sq K₀ L₂ L₃ := sorry

/-- The based chart sending an isomorphism class of lifts to the obstruction against a chosen
lift. -/
noncomputable def extClass (L0 : Lift π h_sq K₀) (hK : K₀.IsBoundedAbove) :
    IsoClass π h_sq K₀ → Ext⁽(1 : ℤ)⁾(K₀, K₀ ⊗ kernelIdeal0Single π h_sq) :=
  Quotient.lift (fun L ↦ obstruction π h_sq K₀ L0 L) sorry

/-- The based chart computes on representatives as `obstruction`. -/
theorem extClass_mk (L0 L : Lift π h_sq K₀) (hK : K₀.IsBoundedAbove) :
    extClass π h_sq K₀ L0 hK (IsoClass.mk π h_sq K₀ L) = obstruction π h_sq K₀ L0 L := sorry

/-- The based chart sends the class of the chosen lift to zero. -/
theorem extClass_self (L0 : Lift π h_sq K₀) (hK : K₀.IsBoundedAbove) :
    extClass π h_sq K₀ L0 hK (IsoClass.mk π h_sq K₀ L0) = 0 := sorry

/-- Every based obstruction chart on isomorphism classes of bounded-above lifts is bijective. -/
theorem isoClass_extClass_bijective (hK : K₀.IsBoundedAbove) (L0 : Lift π h_sq K₀) :
    Function.Bijective (extClass π h_sq K₀ L0 hK) := sorry

/-- If a bounded-above derived module has a lift, its lift classes have a unique additive
torsor structure whose differences are the comparison obstructions. -/
theorem isoClass_isTorsor (hK : K₀.IsBoundedAbove) (L0 : Lift π h_sq K₀) :
    ∃! t : AddTorsor (Ext⁽(1 : ℤ)⁾(K₀, K₀ ⊗ kernelIdeal0Single π h_sq)) (IsoClass π h_sq K₀),
      ∀ L L' : Lift π h_sq K₀,
        t.toVSub.vsub (IsoClass.mk π h_sq K₀ L') (IsoClass.mk π h_sq K₀ L) =
          obstruction π h_sq K₀ L L' := sorry

end

end RingedSite.Hom.ModuleDerived
