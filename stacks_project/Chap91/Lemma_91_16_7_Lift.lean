module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import stacks_project.Chap91.Lemma_91_16_6_Obstruction

/-!
# Lifts of a bounded-above complex along a square-zero surjection

A lift of `K₀` in `D⁻(𝒪₀)` along a locally surjective square-zero map `π : 𝒪 ⟶ 𝒪₀` is a pair
`(K, α₀)` with `K` in `D⁻(𝒪)` and `α₀ : K ⊗ᴸ 𝒪₀ ≅ K₀` in `D(𝒪₀)`. Automorphisms of a given lift
are the cokernel of a canonical map `Ext⁽-1⁾(K₀, K₀) → Hom(K₀, K₀ ⊗ᴸ ℐ[0])`.
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

/-- A lift of `K₀` along `π` is a bounded-above object of `D(𝒪)` together with an identification
of its derived extension of scalars with `K₀`. -/
structure Lift (h_sq : KernelIdeal.IsSquareZero π)
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) where
  /-- The underlying object of `D⁻(𝒪)`. -/
  object : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)
  /-- The comparison isomorphism `object ⊗ᴸ 𝒪₀ ≅ K₀` in `D(𝒪₀)`. -/
  iso : (tensorO0 π).obj object ≅ K₀
  /-- The underlying object is bounded above. -/
  object_isBoundedAbove : object.IsBoundedAbove

namespace Lift

/-- Assemble a lift from a bounded-above complex and a derived-extension isomorphism. -/
def of {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}
    (object : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (iso : (tensorO0 π).obj object ≅ K₀)
    (object_isBoundedAbove : object.IsBoundedAbove) :
    Lift π h_sq K₀ :=
  ⟨object, iso, object_isBoundedAbove⟩

/-- A lift consists of a bounded-above object of `D(𝒪)` and an isomorphism after `⊗ᴸ 𝒪₀`. -/
theorem spec {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}
    (L : Lift π h_sq K₀) :
    Nonempty ((tensorO0 π).obj L.object ≅ K₀) ∧ L.object.IsBoundedAbove := sorry

/-- `Lift.of` recovers the supplied object and comparison isomorphism. -/
theorem spec_iff {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}
    (object : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (iso : (tensorO0 π).obj object ≅ K₀)
    (h : object.IsBoundedAbove) :
    (of π h_sq object iso h).object = object ∧
      (of π h_sq object iso h).iso = iso := sorry

end Lift

variable {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}

/-- A morphism of lifts is a map of underlying objects compatible with the comparison isomorphisms. -/
structure LiftHom (L₁ L₂ : Lift π h_sq K₀) where
  /-- The underlying morphism in `D(𝒪)`. -/
  hom : L₁.object ⟶ L₂.object
  /-- Derived extension of scalars intertwines the comparison isomorphisms. -/
  comm : (tensorO0 π).map hom ≫ L₂.iso.hom = L₁.iso.hom

/-- Assemble a morphism of lifts from a compatible map of underlying objects. -/
def LiftHom.of (L₁ L₂ : Lift π h_sq K₀) (hom : L₁.object ⟶ L₂.object)
    (comm : (tensorO0 π).map hom ≫ L₂.iso.hom = L₁.iso.hom) :
    LiftHom π h_sq L₁ L₂ :=
  ⟨hom, comm⟩

/-- The compatibility square of a morphism of lifts. -/
theorem LiftHom.comm_spec {L₁ L₂ : Lift π h_sq K₀} (φ : LiftHom π h_sq L₁ L₂) :
    (tensorO0 π).map φ.hom ≫ L₂.iso.hom = L₁.iso.hom := sorry

/-- An isomorphism of lifts is an isomorphism of underlying objects compatible with the
comparison isomorphisms. -/
structure LiftIso (L₁ L₂ : Lift π h_sq K₀) where
  /-- The underlying isomorphism in `D(𝒪)`. -/
  iso : L₁.object ≅ L₂.object
  /-- Derived extension of scalars intertwines the comparison isomorphisms. -/
  comm : (tensorO0 π).map iso.hom ≫ L₂.iso.hom = L₁.iso.hom

/-- Assemble an isomorphism of lifts from a compatible isomorphism of underlying objects. -/
def LiftIso.of (L₁ L₂ : Lift π h_sq K₀) (iso : L₁.object ≅ L₂.object)
    (comm : (tensorO0 π).map iso.hom ≫ L₂.iso.hom = L₁.iso.hom) :
    LiftIso π h_sq L₁ L₂ :=
  ⟨iso, comm⟩

/-- The compatibility square of an isomorphism of lifts. -/
theorem LiftIso.comm_spec {L₁ L₂ : Lift π h_sq K₀} (φ : LiftIso π h_sq L₁ L₂) :
    (tensorO0 π).map φ.iso.hom ≫ L₂.iso.hom = L₁.iso.hom := sorry

variable {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}

/-- Automorphisms of a lift `(K, α₀)` are endomorphisms `φ : K ⟶ K` in `D(𝒪)` with
`φ ⊗ᴸ id = id`. -/
def Aut (L : Lift π h_sq K₀) :=
  {φ : L.object ⟶ L.object // (tensorO0 π).map φ = 𝟙 _}

/-- Canonical identification of `𝒪[0]` with the K-flat derived tensor unit of `D(𝒪)`. -/
noncomputable def structureSheafSingleIso :
    structureSheafSingle ≅
      𝟙_ (ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :=
  (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).mapIso
      unitIsoTensorUnit ≪≫
    (singleFunctorIsoCompQ
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).app
      (𝟙_ (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))) ≪≫
    (quotientCompQhIso
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))).symm.app
      (HomologicalComplex.tensorUnit
        (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (up ℤ)) ≪≫
    CategoryTheory.DerivedCategory.KFlat.mapUnitIso.symm

/-- Same-site derived restriction of scalars is an isomorphism on the degree-zero single of the
descended kernel ideal. -/
theorem isIso_pushforwardKernelSingle :
    IsIso (pushforwardSingleUnit π (kernelIdeal0 π h_sq)) := sorry

/-- Comparison from the underived degree-zero single of `π_* ℐ` to derived restriction of scalars. -/
noncomputable def pushforwardKernelSingleIso :
    (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).obj
        ((sameSiteHom π).modulePushforward.{w}.obj (kernelIdeal0 π h_sq)) ≅
      (pushforwardO0 π).obj (kernelIdeal0Single π h_sq) :=
  @asIso _ _ _ _ (pushforwardSingleUnit π (kernelIdeal0 π h_sq))
    (isIso_pushforwardKernelSingle π h_sq)

/-- Derived restriction of the descended kernel ideal is the kernel ideal sheaf in `D(𝒪)`. -/
noncomputable def kernelPushforwardIso :
    (pushforwardO0 π).obj (kernelIdeal0Single π h_sq) ≅ kernelSheafSingle π :=
  (pushforwardKernelSingleIso π h_sq).symm ≪≫ kernelSheafSingleIso π h_sq

/-- The kernel-triangle inclusion `K ⊗ ℐ ⟶ K` obtained by tensoring `KernelIdeal.ι` and the
unitors. -/
noncomputable def kernelTensorInclusion
    (K : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) :
    K ⊗ kernelSheafSingle π ⟶ K :=
  (K ◁ (singleFunctor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) (0 : ℤ)).map
      (KernelIdeal.ι π)) ≫
    (K ◁ structureSheafSingleIso.hom) ≫ (ρ_ K).hom

/-- The endomorphism of a lift obtained by adjoining `f : K₀ ⟶ K₀ ⊗ ℐ[0]` along the kernel
triangle. -/
noncomputable def adjunctInclusion (L : Lift π h_sq K₀)
    (f : K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) :
    L.object ⟶ L.object :=
  ((moduleDerivedAdjunction.{w} (sameSiteHom π)).homEquiv L.object
        ((tensorO0 π).obj L.object ⊗ kernelIdeal0Single π h_sq)
      (L.iso.hom ≫ f ≫ (L.iso.inv ▷ kernelIdeal0Single π h_sq))) ≫
    tensorPushforwardInv π L.object (kernelIdeal0Single π h_sq) ≫
      (L.object ◁ (kernelPushforwardIso π h_sq).hom) ≫
        kernelTensorInclusion π L.object

/-- Send `f : Hom_{𝒪₀}(K₀, K₀ ⊗ᴸ ℐ)` to the automorphism `𝟙 +` the kernel-triangle adjunct. -/
noncomputable def ofHom (L : Lift π h_sq K₀)
    (f : K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) : Aut π h_sq L :=
  ⟨𝟙 L.object + adjunctInclusion π h_sq L f, sorry⟩

/-- `ofHom` is identity plus the kernel-triangle adjunct of `f`. -/
theorem ofHom_spec (L : Lift π h_sq K₀)
    (f : K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) :
    (ofHom π h_sq L f).val = 𝟙 L.object + adjunctInclusion π h_sq L f := sorry

/-- The connecting class of a lift, as the obstruction of the identity map of `K ⊗ᴸ 𝒪₀`
transported to `Ext⁽1⁾(K₀, K₀ ⊗ ℐ[0])`. -/
noncomputable def connectingClass (L : Lift π h_sq K₀) :
    Ext⁽(1 : ℤ)⁾(K₀, K₀ ⊗ kernelIdeal0Single π h_sq) :=
  L.iso.inv ≫ mapObstruction π h_sq (𝟙 ((tensorO0 π).obj L.object)) ≫
    ((L.iso.hom ▷ kernelIdeal0Single π h_sq)⟦(1 : ℤ)⟧')

/-- `connectingClass` is the transport of `mapObstruction` of the identity along `L.iso`. -/
theorem connectingClass_spec (L : Lift π h_sq K₀) :
    connectingClass π h_sq L =
      L.iso.inv ≫ mapObstruction π h_sq (𝟙 ((tensorO0 π).obj L.object)) ≫
        ((L.iso.hom ▷ kernelIdeal0Single π h_sq)⟦(1 : ℤ)⟧') := sorry

/-- The canonical map `Ext⁽-1⁾_{𝒪₀}(K₀, K₀) ⟶ Hom_{𝒪₀}(K₀, K₀ ⊗ᴸ ℐ)` whose cokernel is `Aut`. -/
noncomputable def autDelta (L : Lift π h_sq K₀) :
    Ext⁽(-1 : ℤ)⁾(K₀, K₀) →+ (K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) :=
  AddMonoidHom.mk'
    (fun ξ ↦ (ShiftedHom.homEquiv (0 : ℤ) rfl).symm
      (ShiftedHom.comp ξ (connectingClass π h_sq L) (add_neg_cancel (1 : ℤ))))
    sorry

/-- `autDelta` is postcomposition with the rotated connecting class of the lift. -/
theorem autDelta_spec (L : Lift π h_sq K₀)
    (ξ : Ext⁽(-1 : ℤ)⁾(K₀, K₀)) :
    autDelta π h_sq L ξ =
      (ShiftedHom.homEquiv (0 : ℤ) rfl).symm
        (ShiftedHom.comp ξ (connectingClass π h_sq L) (add_neg_cancel (1 : ℤ))) := sorry

/-- `ofHom` sends the image of `autDelta` to the identity automorphism. -/
theorem ofHom_comp_autDelta (L : Lift π h_sq K₀)
    (ξ : Ext⁽(-1 : ℤ)⁾(K₀, K₀)) :
    (ofHom π h_sq L (autDelta π h_sq L ξ)).val = 𝟙 L.object := sorry

/-- The cokernel of `autDelta`, as the quotient of `Hom_{𝒪₀}(K₀, K₀ ⊗ᴸ ℐ)` by the range. -/
noncomputable abbrev autCoker (L : Lift π h_sq K₀) :=
  (K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) ⧸ (autDelta π h_sq L).range

/-- The canonical map from the cokernel of `autDelta` to automorphisms of the lift. -/
noncomputable def ofCoker (L : Lift π h_sq K₀) : autCoker π h_sq L → Aut π h_sq L :=
  Quotient.lift (ofHom π h_sq L) sorry

/-- `ofCoker` computes on residue classes of homomorphisms. -/
theorem ofCoker_mk (L : Lift π h_sq K₀)
    (f : K₀ ⟶ K₀ ⊗ kernelIdeal0Single π h_sq) :
    ofCoker π h_sq L (Quotient.mk _ f) = ofHom π h_sq L f := sorry

/-- The induced map from the cokernel of `autDelta` to `Aut` is bijective. -/
theorem ofCoker_bijective (L : Lift π h_sq K₀) (hK : K₀.IsBoundedAbove) :
    Function.Bijective (ofCoker π h_sq L) := sorry

end

end RingedSite.Hom.ModuleDerived
