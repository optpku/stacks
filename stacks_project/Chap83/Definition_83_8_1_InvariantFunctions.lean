module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap78.Definition_78_4_1_PreRelation

/-!
# Sheaf of R-invariant functions

For an `R`-invariant morphism `φ : U ⟶ X` of algebraic spaces over `B`, the sheaf of
`R`-invariant functions on `X_étale` is the equalizer of `φ_* s^♯` and `φ_* t^♯`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The associator identifying `T' ×_T (T ×_X W)` with `T' ×_X W` in the spaces étale
site of `T'`. -/
def ringPushforwardPrecompAssocInv {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X) :
    (spacesEtalePullback a).obj ((etaleBaseChange f).obj W) ⟶
      (etaleBaseChange (a ≫ f)).obj W :=
  (spacesEtalePullback a).map
      ((smallEtaleInclusion_comp_spacesEtalePullback f).inv.app W) ≫
    (spacesEtalePullbackComp a f).inv.app ((smallEtaleInclusion X).obj W) ≫
    (smallEtaleInclusion_comp_spacesEtalePullback (a ≫ f)).hom.app W

/-- `ringPushforwardPrecompAssocInv` is the composite of the spaces-étale pullback
comparison, the fibre-product associator, and the étale-base-change iso. -/
theorem ringPushforwardPrecompAssocInv_eq {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X) :
    ringPushforwardPrecompAssocInv a f W =
      (spacesEtalePullback a).map
          ((smallEtaleInclusion_comp_spacesEtalePullback f).inv.app W) ≫
        (spacesEtalePullbackComp a f).inv.app ((smallEtaleInclusion X).obj W) ≫
        (smallEtaleInclusion_comp_spacesEtalePullback (a ≫ f)).hom.app W :=
  sorry

/-- The morphism `T' ×_T U ⟶ T' ×_X W` associated to an arrow `U ⟶ T ×_X W`. -/
def ringPushforwardPrecompStructuredArrowHom {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X)
    (α : StructuredArrow (op ((etaleBaseChange f).obj W)) (smallEtaleInclusion T).op) :
    (etaleBaseChange a).obj α.right.unop ⟶ (etaleBaseChange (a ≫ f)).obj W :=
  (smallEtaleInclusion_comp_spacesEtalePullback a).inv.app α.right.unop ≫
    (spacesEtalePullback a).map α.hom.unop ≫
    ringPushforwardPrecompAssocInv a f W

/-- `ringPushforwardPrecompStructuredArrowHom` is the composite of the small-étale
comparison, the image of the structured arrow, and the associator. -/
theorem ringPushforwardPrecompStructuredArrowHom_eq {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X)
    (α : StructuredArrow (op ((etaleBaseChange f).obj W)) (smallEtaleInclusion T).op) :
    ringPushforwardPrecompStructuredArrowHom a f W α =
      (smallEtaleInclusion_comp_spacesEtalePullback a).inv.app α.right.unop ≫
        (spacesEtalePullback a).map α.hom.unop ≫
        ringPushforwardPrecompAssocInv a f W :=
  sorry

/-- The cone of Kan-counit components presenting `(a ≫ f)_* 𝒪_{T'} ⟶ f_* (a_* 𝒪_{T'})`
at `W`. -/
def ringPushforwardPrecompCounitCone {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj W))
        (smallEtaleInclusion T).op ⋙
          ((ringPushforward a).obj (structureSheaf T')).obj) where
  pt := ((ringPushforward (a ≫ f)).obj (structureSheaf T')).obj.obj (op W)
  π :=
    { app := fun α ↦
        ((smallEtaleInclusion T').op.ran.obj (structureSheaf T').obj).map
          (op (ringPushforwardPrecompStructuredArrowHom a f W α))
      naturality := fun _ _ _ ↦ sorry }

/-- The apex of `ringPushforwardPrecompCounitCone` is `(a ≫ f)_* 𝒪_{T'}` at `W`. -/
theorem ringPushforwardPrecompCounitCone_pt {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : smallEtaleSite X) :
    (ringPushforwardPrecompCounitCone a f W).pt =
      ((ringPushforward (a ≫ f)).obj (structureSheaf T')).obj.obj (op W) :=
  sorry

/-- The component at `W` of the Kan-counit comparison `(a ≫ f)_* 𝒪_{T'} ⟶ f_* (a_* 𝒪_{T'})`. -/
def ringPushforwardPrecompCounit_app {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : (smallEtaleSite X)ᵒᵖ) :
    ((ringPushforward (a ≫ f)).obj (structureSheaf T')).obj.obj W ⟶
      ((ringPushforward f).obj ((ringPushforward a).obj (structureSheaf T'))).obj.obj W :=
  limit.lift _ (ringPushforwardPrecompCounitCone a f W.unop) ≫
    ((smallEtaleInclusion T).op.ranObjObjIsoLimit
        ((ringPushforward a).obj (structureSheaf T')).obj
        (op ((etaleBaseChange f).obj W.unop))).inv

/-- `ringPushforwardPrecompCounit_app a f W` is the limit-lift of the Kan-counit cone. -/
theorem ringPushforwardPrecompCounit_app_eq {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : (smallEtaleSite X)ᵒᵖ) :
    ringPushforwardPrecompCounit_app a f W =
      limit.lift _ (ringPushforwardPrecompCounitCone a f W.unop) ≫
        ((smallEtaleInclusion T).op.ranObjObjIsoLimit
            ((ringPushforward a).obj (structureSheaf T')).obj
            (op ((etaleBaseChange f).obj W.unop))).inv :=
  sorry

/-- The Kan-counit comparison `(a ≫ f)_* 𝒪_{T'} ⟶ f_* (a_* 𝒪_{T'})`, obtained from pullback
associativity and the pointwise limit formula for the right Kan extension. -/
def ringPushforwardPrecompCounit {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) :
    (ringPushforward (a ≫ f)).obj (structureSheaf T') ⟶
      (ringPushforward f).obj ((ringPushforward a).obj (structureSheaf T')) :=
  InducedCategory.homMk
    { app := fun W ↦ ringPushforwardPrecompCounit_app a f W
      naturality := fun _ _ _ ↦ sorry }

/-- The component at `W` of `ringPushforwardPrecompCounit` is
`ringPushforwardPrecompCounit_app`. -/
theorem ringPushforwardPrecompCounit_hom_app {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) (W : (smallEtaleSite X)ᵒᵖ) :
    (ringPushforwardPrecompCounit a f).hom.app W =
      ringPushforwardPrecompCounit_app a f W :=
  sorry

/-- The Kan-counit comparison is an isomorphism of ring sheaves. -/
instance ringPushforwardPrecompCounit_isIso {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) :
    IsIso (ringPushforwardPrecompCounit a f) :=
  sorry

/-- Comparison `f_* (a_* 𝒪_{T'}) ⟶ (a ≫ f)_* 𝒪_{T'}` obtained by inverting the Kan-counit
associator. -/
def ringPushforwardPrecomp {T T' X : AlgebraicSpace S} (a : T' ⟶ T) (f : T ⟶ X) :
    (ringPushforward f).obj ((ringPushforward a).obj (structureSheaf T')) ⟶
      (ringPushforward (a ≫ f)).obj (structureSheaf T') :=
  inv (ringPushforwardPrecompCounit a f)

/-- `ringPushforwardPrecomp` is the inverse of the Kan-counit comparison. -/
theorem ringPushforwardPrecomp_eq {T T' X : AlgebraicSpace S}
    (a : T' ⟶ T) (f : T ⟶ X) :
    ringPushforwardPrecomp a f = inv (ringPushforwardPrecompCounit a f) :=
  sorry

namespace PreRelation

/-- The map `φ_* s^♯ : φ_* 𝒪_U ⟶ (φ ∘ s)_* 𝒪_R` on `X_étale`. -/
def sourceSharpPushforward {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    (ringPushforward φ.left).obj (structureSheaf U.left) ⟶
      (ringPushforward (P.s.left ≫ φ.left)).obj (structureSheaf P.left.left) :=
  (ringPushforward φ.left).map (structureSheafMap P.s.left) ≫
    ringPushforwardPrecomp P.s.left φ.left

/-- `sourceSharpPushforward` is pushforward of `s^♯` followed by the associator. -/
theorem sourceSharpPushforward_eq {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    P.sourceSharpPushforward φ =
      (ringPushforward φ.left).map (structureSheafMap P.s.left) ≫
        ringPushforwardPrecomp P.s.left φ.left :=
  sorry

/-- Transport of `(φ ∘ t)_* 𝒪_R` to `(φ ∘ s)_* 𝒪_R` along `R`-invariance. -/
def targetDirectImageIso {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    (ringPushforward (P.t.left ≫ φ.left)).obj (structureSheaf P.left.left) ≅
      (ringPushforward (P.s.left ≫ φ.left)).obj (structureSheaf P.left.left) :=
  eqToIso (congrArg (fun g ↦ (ringPushforward g).obj (structureSheaf P.left.left))
    (congrArg (fun ψ : P.left ⟶ X ↦ ψ.left) h))

/-- `targetDirectImageIso` is the identity transport along the underlying equality
`P.t.left ≫ φ.left = P.s.left ≫ φ.left`. -/
theorem targetDirectImageIso_eq {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.targetDirectImageIso φ h =
      eqToIso (congrArg (fun g ↦ (ringPushforward g).obj (structureSheaf P.left.left))
        (congrArg (fun ψ : P.left ⟶ X ↦ ψ.left) h)) :=
  sorry

/-- The map `φ_* t^♯ : φ_* 𝒪_U ⟶ (φ ∘ s)_* 𝒪_R` on `X_étale`, after transporting the
target along `R`-invariance. -/
def targetSharpPushforward {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    (ringPushforward φ.left).obj (structureSheaf U.left) ⟶
      (ringPushforward (P.s.left ≫ φ.left)).obj (structureSheaf P.left.left) :=
  (ringPushforward φ.left).map (structureSheafMap P.t.left) ≫
    ringPushforwardPrecomp P.t.left φ.left ≫ (P.targetDirectImageIso φ h).hom

/-- `targetSharpPushforward` is pushforward of `t^♯`, the associator, and invariance
transport. -/
theorem targetSharpPushforward_eq {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.targetSharpPushforward φ h =
      (ringPushforward φ.left).map (structureSheafMap P.t.left) ≫
        ringPushforwardPrecomp P.t.left φ.left ≫ (P.targetDirectImageIso φ h).hom :=
  sorry

/-- The sheaf of `R`-invariant functions `(φ_* 𝒪_U)^R` on `X_étale`, as the equalizer of
`φ_* s^♯` and `φ_* t^♯`. -/
def invariantFunctions {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    Sheaf (smallEtaleTopology X.left) RingCat.{u} :=
  equalizer (P.sourceSharpPushforward φ) (P.targetSharpPushforward φ h)

/-- `invariantFunctions` is the equalizer of `sourceSharpPushforward` and
`targetSharpPushforward`. -/
theorem invariantFunctions_eq {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.invariantFunctions φ h =
      equalizer (P.sourceSharpPushforward φ) (P.targetSharpPushforward φ h) :=
  sorry

/-- The inclusion `(φ_* 𝒪_U)^R ⟶ φ_* 𝒪_U` of the sheaf of `R`-invariant functions. -/
def invariantFunctionsι {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.invariantFunctions φ h ⟶ (ringPushforward φ.left).obj (structureSheaf U.left) :=
  equalizer.ι (P.sourceSharpPushforward φ) (P.targetSharpPushforward φ h)

/-- The equalizer inclusion equalizes `φ_* s^♯` and `φ_* t^♯`. -/
theorem invariantFunctionsι_equalizes {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.invariantFunctionsι φ h ≫ P.sourceSharpPushforward φ =
      P.invariantFunctionsι φ h ≫ P.targetSharpPushforward φ h :=
  sorry

/-- The structure map `φ^♯` equalizes `φ_* s^♯` and `φ_* t^♯`. -/
theorem structureSheafMap_equalizes {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    structureSheafMap φ.left ≫ P.sourceSharpPushforward φ =
      structureSheafMap φ.left ≫ P.targetSharpPushforward φ h :=
  sorry

/-- The natural map `𝒪_X ⟶ (φ_* 𝒪_U)^R` factoring `φ^♯` through the equalizer of
`R`-invariant functions. -/
def structureSheafToInvariantFunctions {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    structureSheaf X.left ⟶ P.invariantFunctions φ h :=
  equalizer.lift (structureSheafMap φ.left) (P.structureSheafMap_equalizes φ h)

/-- The natural map composed with the equalizer inclusion recovers `φ^♯`. -/
theorem structureSheafToInvariantFunctions_comp_ι {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.structureSheafToInvariantFunctions φ h ≫ P.invariantFunctionsι φ h =
      structureSheafMap φ.left :=
  sorry

/-- The functions on `X` are the `R`-invariant functions on `U` when
`𝒪_X ⟶ (φ_* 𝒪_U)^R` is an isomorphism. -/
def HasInvariantFunctions {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) : Prop :=
  IsIso (P.structureSheafToInvariantFunctions φ h)

/-- `HasInvariantFunctions` is precisely the assertion that the natural map is an
isomorphism. -/
theorem hasInvariantFunctions_iff {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) (h : P.t ≫ φ = P.s ≫ φ) :
    P.HasInvariantFunctions φ h ↔ IsIso (P.structureSheafToInvariantFunctions φ h) :=
  sorry

end PreRelation

end AlgebraicGeometry.AlgebraicSpace
