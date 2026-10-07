module

public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import stacks_project.Chap75.Lemma_75_21_1_Pullback

/-!
# Derived fibre and base-change pullbacks

For a morphism `f : X ⟶ Y` of algebraic spaces, derived pullback of an object
of `D(𝒪_X)` to a field-valued fibre `X_y` or to a base change `X_V` is derived
pullback along the first projection of the corresponding fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Derived pullback of `K` to the field-valued fibre `X_y`. -/
def fiberPullback (f : X ⟶ Y) (p : FieldValuedPoint Y) (K : ModuleDerived X) :
    ModuleDerived (fieldFiber f p) :=
  (pullback (fieldFiberι f p)).obj K

/-- `fiberPullback f p K` is derived pullback of `K` along `fieldFiberι f p`. -/
theorem fiberPullback_eq (f : X ⟶ Y) (p : FieldValuedPoint Y) (K : ModuleDerived X) :
    fiberPullback f p K = (pullback (fieldFiberι f p)).obj K :=
  sorry

/-- Derived pullback of `K` to the base change `X_V = X ×_Y V`. -/
def baseChangePullback (f : X ⟶ Y) {V : AlgebraicSpace S} (g : V ⟶ Y)
    (K : ModuleDerived X) : ModuleDerived (Limits.pullback f g) :=
  (pullback (Limits.pullback.fst f g)).obj K

/-- `baseChangePullback f g K` is derived pullback of `K` along `X_V ⟶ X`. -/
theorem baseChangePullback_eq (f : X ⟶ Y) {V : AlgebraicSpace S} (g : V ⟶ Y)
    (K : ModuleDerived X) :
    baseChangePullback f g K = (pullback (Limits.pullback.fst f g)).obj K :=
  sorry

/-- The canonical map `X_{V'} ⟶ X_V` induced by a morphism `V' ⟶ V` over `Y`. -/
def baseChangeSpaceMap (f : X ⟶ Y) {V V' : AlgebraicSpace S} {g : V ⟶ Y}
    {g' : V' ⟶ Y} (φ : V' ⟶ V) (hφ : φ ≫ g = g') :
    Limits.pullback f g' ⟶ Limits.pullback f g :=
  Limits.pullback.lift (Limits.pullback.fst f g') (Limits.pullback.snd f g' ≫ φ)
    ((Limits.pullback.condition).trans
      ((congrArg (fun k ↦ Limits.pullback.snd f g' ≫ k) hφ.symm).trans
        (Category.assoc (Limits.pullback.snd f g') φ g).symm))

/-- The map `baseChangeSpaceMap f φ hφ` commutes with the projections to `X`. -/
theorem baseChangeSpaceMap_fst (f : X ⟶ Y) {V V' : AlgebraicSpace S} {g : V ⟶ Y}
    {g' : V' ⟶ Y} (φ : V' ⟶ V) (hφ : φ ≫ g = g') :
    baseChangeSpaceMap f φ hφ ≫ Limits.pullback.fst f g = Limits.pullback.fst f g' :=
  sorry

/-- The map `baseChangeSpaceMap f φ hφ` commutes with the projections to the varying base. -/
theorem baseChangeSpaceMap_snd (f : X ⟶ Y) {V V' : AlgebraicSpace S} {g : V ⟶ Y}
    {g' : V' ⟶ Y} (φ : V' ⟶ V) (hφ : φ ≫ g = g') :
    baseChangeSpaceMap f φ hφ ≫ Limits.pullback.snd f g =
      Limits.pullback.snd f g' ≫ φ :=
  sorry

/-- The comparison identifying `K_{V'}` with the derived pullback of `K_V` along
`X_{V'} ⟶ X_V`. -/
def baseChangePullbackRestrict (f : X ⟶ Y) {V V' : AlgebraicSpace S} {g : V ⟶ Y}
    {g' : V' ⟶ Y} (φ : V' ⟶ V) (hφ : φ ≫ g = g') (K : ModuleDerived X) :
    baseChangePullback f g' K ≅
      (pullback (baseChangeSpaceMap f φ hφ)).obj (baseChangePullback f g K) :=
  (pullbackCongr
      ((Limits.pullback.lift_fst (Limits.pullback.fst f g')
          (Limits.pullback.snd f g' ≫ φ)
          ((Limits.pullback.condition).trans
            ((congrArg (fun k ↦ Limits.pullback.snd f g' ≫ k) hφ.symm).trans
              (Category.assoc (Limits.pullback.snd f g') φ g).symm))).symm)).app K ≪≫
    (pullbackCompIso (baseChangeSpaceMap f φ hφ) (Limits.pullback.fst f g)).symm.app K

/-- The forward map of `baseChangePullbackRestrict` is the composition comparison
through `X_{V'} ⟶ X_V ⟶ X`. -/
theorem baseChangePullbackRestrict_hom (f : X ⟶ Y) {V V' : AlgebraicSpace S}
    {g : V ⟶ Y} {g' : V' ⟶ Y} (φ : V' ⟶ V) (hφ : φ ≫ g = g') (K : ModuleDerived X) :
    (baseChangePullbackRestrict f φ hφ K).hom =
      (pullbackCongr (baseChangeSpaceMap_fst f φ hφ).symm).hom.app K ≫
        (pullbackCompIso (baseChangeSpaceMap f φ hφ)
            (Limits.pullback.fst f g)).inv.app K :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
