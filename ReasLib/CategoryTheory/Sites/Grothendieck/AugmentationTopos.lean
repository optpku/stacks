module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmentation
public import ReasLib.CategoryTheory.Sites.Grothendieck.SheafComparison
public import ReasLib.CategoryTheory.Sites.Grothendieck.LowerShriek

/-!
# Augmentation morphisms of topoi, fiberwise case

A cocontinuous augmentation `u0` of a fiberwise simplicial site induces stage
morphisms of topoi `a_n` and a total morphism `a : Sh(C_total) ⟶ Sh(D)` whose
inverse image is the sheaf system of the functors `a_n⁻¹` and whose direct image
is the equalizer of the two coface maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`. The total
morphism is presented by the cocontinuous functor sending a degree-`n` object
`U` to `u_n(U)`.
-/

-- Public constructions use private component maps without adding public implementation API.
set_option backward.privateInPublic true

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
include h_fiberwise
include h_aug


namespace IsAugmentation

/-- The common composite `u_n = u0 ∘ u_φ` is cocontinuous. -/
instance stageFunctor_isCocontinuous (n : SimplexCategory) :
    (stageFunctor F u0 n).IsCocontinuous
      (J (op n)).toGrothendieck K.toGrothendieck :=
  sorry

/-- Identification `u_φ ⋙ u_m ≅ u_n` of presenting functors along a simplex operator. -/
def stageFunctor_compIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (F.map φ.op).toFunctor ⋙ stageFunctor F u0 m ≅
      stageFunctor F u0 n :=
  (Functor.associator (F.map φ.op).toFunctor
      ((F.map (SimplexCategory.const ⦋0⦌ m 0).op).toFunctor) u0).symm ≪≫
    NatIso.hcomp (map_comp_toFunctor F (SimplexCategory.const ⦋0⦌ m 0) φ) (Iso.refl u0) ≪≫
    eqToIso (h_aug.map_eq (SimplexCategory.const ⦋0⦌ m 0 ≫ φ)
      (SimplexCategory.const ⦋0⦌ n 0))

/-- The morphism of topoi `a_n : Sh(C_n) ⟶ Sh(D)` presented by the common
composite `u_n`. -/
def stageTopos (n : SimplexCategory) :
    MorphismOfTopoiIn K.toGrothendieck (J (op n)).toGrothendieck :=
  (stageFunctor F u0 n).morphismOfTopoiInOfCocontinuous
    (J (op n)).toGrothendieck K.toGrothendieck

/-- Inverse image of `a_n` is cocontinuous sheaf pullback along `u_n`. -/
theorem stageTopos_inverseImage (n : SimplexCategory) :
    (stageTopos F J K u0 n)⁻¹ =
      (stageFunctor F u0 n).sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck K.toGrothendieck :=
  rfl

/-- Direct image of `a_n` is cocontinuous sheaf pushforward along `u_n`. -/
theorem stageTopos_pushforward (n : SimplexCategory) :
    (stageTopos F J K u0 n).pushforward =
      (stageFunctor F u0 n).sheafPushforwardCocontinuous (Type w)
        (J (op n)).toGrothendieck K.toGrothendieck :=
  rfl

/-- Inverse-image form of `a_m ∘ f_φ = a_n`. -/
def stageTopos_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageTopos F J K u0 m)⁻¹ ⋙ (Grothendieck.toposMap F J φ)⁻¹ ≅
      (stageTopos F J K u0 n)⁻¹ :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        ((stageFunctor F u0 m).sheafPullbackCocontinuousAdjunction
          (J (op m)).toGrothendieck K.toGrothendieck)
        ((F.map φ.op).toFunctor.sheafPullbackCocontinuousAdjunction
          (J (op n)).toGrothendieck (J (op m)).toGrothendieck)).ofNatIsoRight
      (Functor.sheafPushforwardCocontinuousComp'
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck K.toGrothendieck
        (F.map φ.op).toFunctor (stageFunctor F u0 m)
        (stageFunctor_compIso F J K u0 φ)))
    ((stageFunctor F u0 n).sheafPullbackCocontinuousAdjunction
      (J (op n)).toGrothendieck K.toGrothendieck)

/-- Direct-image mate of `a_m ∘ f_φ = a_n`. -/
def stageTopos_pushforward_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (Grothendieck.toposMap F J φ).pushforward ⋙ (stageTopos F J K u0 m).pushforward ≅
      (stageTopos F J K u0 n).pushforward :=
  MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
    (MorphismOfTopoiIn.comp (stageTopos F J K u0 m) (Grothendieck.toposMap F J φ))
    (stageTopos F J K u0 n)
    (stageTopos_comp F J K u0 φ)

/-- Pushforward-form transition of the inverse-image sheaf system at a simplex operator. -/
private def inverseImageSystemMap (G : Sheaf K.toGrothendieck (Type w))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageTopos F J K u0 m)⁻¹.obj G ⟶
      (Grothendieck.toposMap F J φ).pushforward.obj
        ((stageTopos F J K u0 n)⁻¹.obj G) :=
  ((Grothendieck.toposMap F J φ).adjunction.homEquiv
      ((stageTopos F J K u0 m)⁻¹.obj G)
      ((stageTopos F J K u0 n)⁻¹.obj G))
    ((stageTopos_comp F J K u0 φ).hom.app G)

/-- The stagewise inverse-image transitions respect identities and composition. -/
private theorem inverseImageSystem_obj_laws
    (G : Sheaf K.toGrothendieck (Type w)) :
    (∀ n : SimplexCategory,
      inverseImageSystemMap F J K u0 G (𝟙 n) =
        (SimplicialSites.HasPushforwardFunctoriality.pushforwardIdIso
          (J := fun n ↦ (J (op n)).toGrothendieck) (fHom := fun φ ↦ Grothendieck.toposMap F J φ) n).inv.app
            ((stageTopos F J K u0 n)⁻¹.obj G)) ∧
    (∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      inverseImageSystemMap F J K u0 G (ψ ≫ φ) =
        inverseImageSystemMap F J K u0 G ψ ≫ (Grothendieck.toposMap F J ψ).pushforward.map
          (inverseImageSystemMap F J K u0 G φ) ≫
          (SimplicialSites.HasPushforwardFunctoriality.pushforwardCompIso
            (J := fun n ↦ (J (op n)).toGrothendieck) (fHom := fun φ ↦ Grothendieck.toposMap F J φ)
            ψ φ).hom.app ((stageTopos F J K u0 n)⁻¹.obj G)) := by
  sorry

/-- Stage inverse images of a sheaf morphism commute with the system transitions. -/
private theorem inverseImageSystem_map_naturality
    {G H : Sheaf K.toGrothendieck (Type w)} (α : G ⟶ H)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    inverseImageSystemMap F J K u0 G φ ≫ (Grothendieck.toposMap F J φ).pushforward.map
        ((stageTopos F J K u0 n)⁻¹.map α) =
      (stageTopos F J K u0 m)⁻¹.map α ≫
        inverseImageSystemMap F J K u0 H φ := by
  sorry

/-- The sheaf system whose stage sheaves are `a_n⁻¹ G` and whose transitions are the
identifications `f_φ⁻¹ a_m⁻¹ G ≅ a_n⁻¹ G`. -/
def inverseImageSystem :
    Sheaf K.toGrothendieck (Type w) ⥤
      SimplicialSites.SheafSystem (fun n ↦ (J (op n)).toGrothendieck)
        (fun φ ↦ Grothendieck.toposMap F J φ) where
  obj G :=
    SimplicialSites.SheafSystem.of
      (fun n ↦ (stageTopos F J K u0 n)⁻¹.obj G)
      (fun {m n} φ ↦ inverseImageSystemMap F J K u0 G φ) ((inverseImageSystem_obj_laws F J K u0 G).1)
      ((inverseImageSystem_obj_laws F J K u0 G).2)
  map {G H} α :=
    SimplicialSites.SheafSystem.homMk
      (fun n ↦ (stageTopos F J K u0 n)⁻¹.map α) (inverseImageSystem_map_naturality F J K u0 α)
  map_id := by
    intro G
    apply SimplicialSites.SheafSystem.Hom.ext
    intro n
    exact (stageTopos F J K u0 n)⁻¹.map_id G
  map_comp := by
    intro G H L α β
    apply SimplicialSites.SheafSystem.Hom.ext
    intro n
    exact (stageTopos F J K u0 n)⁻¹.map_comp α β

/-- The stage sheaf of `inverseImageSystem.obj G` at `n` is `a_n⁻¹ G`. -/
theorem inverseImageSystem_obj (G : Sheaf K.toGrothendieck (Type w))
    (n : SimplexCategory) :
    ((inverseImageSystem F J K u0).obj G).obj n =
      (stageTopos F J K u0 n)⁻¹.obj G :=
  rfl

/-- Inverse image `a⁻¹` of the total augmentation morphism. -/
def inverseImage :
    Sheaf K.toGrothendieck (Type w) ⥤ Sheaf (topology F J) (Type w) :=
  inverseImageSystem F J K u0 ⋙ ofSheafSystem F J

/-- Inverse image of a sheaf `G` is `ofSheafSystem` of the system of the sheaves `a_n⁻¹ G`. -/
theorem inverseImage_obj (G : Sheaf K.toGrothendieck (Type w)) :
    (inverseImage F J K u0).obj G =
      (ofSheafSystem F J).obj ((inverseImageSystem F J K u0).obj G) :=
  rfl

/-- Inverse image `a⁻¹` preserves finite limits. -/
instance inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImage F J K u0) :=
  sorry

/-- The two maps `a_{0,*} F_0 ⇉ a_{1,*} F_1` induced by the coface operators `δ i`. -/
def pushforwardParallel (G : Sheaf (topology F J) (Type w)) (i : Fin 2) :
    (stageTopos F J K u0 ⦋0⦌).pushforward.obj
      (((toSheafSystem F J).obj G).obj ⦋0⦌) ⟶
      (stageTopos F J K u0 ⦋1⦌).pushforward.obj
        (((toSheafSystem F J).obj G).obj ⦋1⦌) :=
  (stageTopos F J K u0 ⦋0⦌).pushforward.map
      ((Grothendieck.toposMap F J (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).adjunction.unit.app
        (((toSheafSystem F J).obj G).obj ⦋0⦌)) ≫
    (stageTopos F J K u0 ⦋0⦌).pushforward.map
      ((Grothendieck.toposMap F J (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).pushforward.map
        (SimplicialSites.SheafSystem.mapInverseImage ((toSheafSystem F J).obj G)
          (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌))) ≫
    (stageTopos_pushforward_comp F J K u0
        (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).hom.app
      (((toSheafSystem F J).obj G).obj ⦋1⦌)

/-- The degree-zero direct image of a morphism preserves the two coface equalities. -/
private theorem pushforward_map_condition
    {G H : Sheaf (topology F J) (Type w)} (α : G ⟶ H) :
    (equalizer.ι (pushforwardParallel F J K u0 G 0)
          (pushforwardParallel F J K u0 G 1) ≫
        (stageTopos F J K u0 ⦋0⦌).pushforward.map
          (((toSheafSystem F J).map α).app ⦋0⦌)) ≫ pushforwardParallel F J K u0 H 0 =
      (equalizer.ι (pushforwardParallel F J K u0 G 0)
          (pushforwardParallel F J K u0 G 1) ≫
        (stageTopos F J K u0 ⦋0⦌).pushforward.map
          (((toSheafSystem F J).map α).app ⦋0⦌)) ≫ pushforwardParallel F J K u0 H 1 := by
  sorry

/-- Direct image `a_*`, sending a sheaf on `C_total` to the equalizer of
`a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
def pushforward :
    Sheaf (topology F J) (Type w) ⥤ Sheaf K.toGrothendieck (Type w) where
  obj G :=
    equalizer (pushforwardParallel F J K u0 G 0)
      (pushforwardParallel F J K u0 G 1)
  map {G H} α :=
    equalizer.lift
      (equalizer.ι (pushforwardParallel F J K u0 G 0)
          (pushforwardParallel F J K u0 G 1) ≫
        (stageTopos F J K u0 ⦋0⦌).pushforward.map
          (((toSheafSystem F J).map α).app ⦋0⦌))
      (pushforward_map_condition F J K u0 α)
  map_id := by
    intro G
    apply equalizer.hom_ext
    simp only [equalizer.lift_ι, Functor.map_id]
    change _ ≫ (stageTopos F J K u0 ⦋0⦌).pushforward.map (𝟙 _) = _
    simp
  map_comp := by
    intro G H L α β
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι]
    change _ ≫ (stageTopos F J K u0 ⦋0⦌).pushforward.map
        (((toSheafSystem F J).map (α ≫ β)).app ⦋0⦌) = _
    rw [(toSheafSystem F J).map_comp]
    change _ ≫ (stageTopos F J K u0 ⦋0⦌).pushforward.map
        ((((toSheafSystem F J).map α).app ⦋0⦌) ≫
          (((toSheafSystem F J).map β).app ⦋0⦌)) = _
    rw [Functor.map_comp]
    simp only [← Category.assoc, equalizer.lift_ι]

/-- The object `a_* G` is the equalizer of the two coface maps. -/
theorem pushforward_obj (G : Sheaf (topology F J) (Type w)) :
    (pushforward F J K u0).obj G =
      equalizer (pushforwardParallel F J K u0 G 0)
        (pushforwardParallel F J K u0 G 1) :=
  rfl

/-- The comparison `a_* G ⟶ a_{0,*} G_0`. -/
def pushforwardι (G : Sheaf (topology F J) (Type w)) :
    (pushforward F J K u0).obj G ⟶
      (stageTopos F J K u0 ⦋0⦌).pushforward.obj
        (((toSheafSystem F J).obj G).obj ⦋0⦌) :=
  equalizer.ι (pushforwardParallel F J K u0 G 0)
    (pushforwardParallel F J K u0 G 1)

/-- The fork presenting `a_* G` as equalizer of `a_{0,*} G_0 ⇉ a_{1,*} G_1`. -/
def pushforwardFork (G : Sheaf (topology F J) (Type w)) :
    Fork (pushforwardParallel F J K u0 G 0)
      (pushforwardParallel F J K u0 G 1) :=
  equalizer.fork (pushforwardParallel F J K u0 G 0)
    (pushforwardParallel F J K u0 G 1)

/-- The two coface maps coequalize `pushforwardι`. -/
theorem pushforwardFork_condition (G : Sheaf (topology F J) (Type w)) :
    pushforwardι F J K u0 G ≫
        pushforwardParallel F J K u0 G 0 =
      pushforwardι F J K u0 G ≫
        pushforwardParallel F J K u0 G 1 :=
  equalizer.condition _ _

/-- `a_* G` is the equalizer of the two maps `a_{0,*} G_0 ⇉ a_{1,*} G_1`. -/
def pushforwardFork_isLimit (G : Sheaf (topology F J) (Type w)) :
    IsLimit (pushforwardFork F J K u0 G) :=
  limit.isLimit
    (parallelPair (pushforwardParallel F J K u0 G 0)
      (pushforwardParallel F J K u0 G 1))

/-- The degree-zero adjoint of a total sheaf map satisfies the coface equality. -/
private theorem homEquivToFun_condition (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w))
    (α : (inverseImage F J K u0).obj H ⟶ G) :
    (((stageTopos F J K u0 ⦋0⦌).adjunction.homEquiv H
        (((toSheafSystem F J).obj G).obj ⦋0⦌))
      (((counitIso F J).inv.app ((inverseImageSystem F J K u0).obj H) ≫
          (toSheafSystem F J).map α).app ⦋0⦌)) ≫ pushforwardParallel F J K u0 G 0 =
      (((stageTopos F J K u0 ⦋0⦌).adjunction.homEquiv H
        (((toSheafSystem F J).obj G).obj ⦋0⦌))
      (((counitIso F J).inv.app ((inverseImageSystem F J K u0).obj H) ≫
          (toSheafSystem F J).map α).app ⦋0⦌)) ≫ pushforwardParallel F J K u0 G 1 := by
  sorry

/-- Degree-zero adjoint of a map `a⁻¹ H ⟶ G`, as a map `H ⟶ a_{0,*} G_0`. -/
private def homEquivToFun (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w))
    (α : (inverseImage F J K u0).obj H ⟶ G) :
    H ⟶ (pushforward F J K u0).obj G :=
  equalizer.lift
    (((stageTopos F J K u0 ⦋0⦌).adjunction.homEquiv H
        (((toSheafSystem F J).obj G).obj ⦋0⦌))
      (((counitIso F J).inv.app ((inverseImageSystem F J K u0).obj H) ≫
          (toSheafSystem F J).map α).app ⦋0⦌))
    (homEquivToFun_condition F J K u0 H G α)

/-- Stage-`n` component of the system map associated to a map `H ⟶ a_* G`. -/
private def homEquivInvFunApp (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w))
    (β : H ⟶ (pushforward F J K u0).obj G) (n : SimplexCategory) :
    (stageTopos F J K u0 n)⁻¹.obj H ⟶
      ((toSheafSystem F J).obj G).obj n :=
  (stageTopos_comp F J K u0 (SimplexCategory.const ⦋0⦌ n 0)).inv.app H ≫
    (Grothendieck.toposMap F J (SimplexCategory.const ⦋0⦌ n 0)).inverseImage.map
      (((stageTopos F J K u0 ⦋0⦌).adjunction.homEquiv H
          (((toSheafSystem F J).obj G).obj ⦋0⦌)).symm
        (β ≫ pushforwardι F J K u0 G)) ≫
    SimplicialSites.SheafSystem.mapInverseImage ((toSheafSystem F J).obj G)
      (SimplexCategory.const ⦋0⦌ n 0)

/-- The components reconstructed from an equalizer map commute with simplex transitions. -/
private theorem homEquivInvFun_naturality (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w))
    (β : H ⟶ (pushforward F J K u0).obj G)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((inverseImageSystem F J K u0).obj H).map φ ≫
        (Grothendieck.toposMap F J φ).pushforward.map
          (homEquivInvFunApp F J K u0 H G β n) =
      homEquivInvFunApp F J K u0 H G β m ≫
        ((toSheafSystem F J).obj G).map φ := by
  sorry

/-- The inverse adjunction map, assembling a morphism `a⁻¹ H ⟶ G` from `H ⟶ a_* G`. -/
private def homEquivInvFun (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w))
    (β : H ⟶ (pushforward F J K u0).obj G) :
    (inverseImage F J K u0).obj H ⟶ G :=
  (ofSheafSystem F J).map
      (SimplicialSites.SheafSystem.homMk
        (homEquivInvFunApp F J K u0 H G β) (homEquivInvFun_naturality F J K u0 H G β)) ≫
    (unitIso F J).inv.app G

/-- The explicit total adjunction maps are inverse to each other. -/
private theorem totalToposHomEquiv_laws (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w)) :
    Function.LeftInverse (homEquivInvFun F J K u0 H G) (homEquivToFun F J K u0 H G) ∧
      Function.RightInverse (homEquivInvFun F J K u0 H G) (homEquivToFun F J K u0 H G) := by
  sorry

/-- Hom-set equivalence `Hom(a⁻¹ H, G) ≃ Hom(H, a_* G)` of the total adjunction. -/
private def totalToposHomEquiv (H : Sheaf K.toGrothendieck (Type w))
    (G : Sheaf (topology F J) (Type w)) :
    ((inverseImage F J K u0).obj H ⟶ G) ≃
      (H ⟶ (pushforward F J K u0).obj G) where
  toFun := homEquivToFun F J K u0 H G
  invFun := homEquivInvFun F J K u0 H G
  left_inv := (totalToposHomEquiv_laws F J K u0 H G).1
  right_inv := (totalToposHomEquiv_laws F J K u0 H G).2

/-- The total Hom equivalence is natural in both sheaf arguments. -/
private theorem totalToposAdjunction_laws :
    (∀ {X' X : Sheaf K.toGrothendieck (Type w)}
      {Y : Sheaf (topology F J) (Type w)}
      (f : X' ⟶ X) (g : X ⟶ (pushforward F J K u0).obj Y),
      (totalToposHomEquiv F J K u0 X' Y).symm (f ≫ g) =
        (inverseImage F J K u0).map f ≫ (totalToposHomEquiv F J K u0 X Y).symm g) ∧
    (∀ {X : Sheaf K.toGrothendieck (Type w)}
      {Y Y' : Sheaf (topology F J) (Type w)}
      (f : (inverseImage F J K u0).obj X ⟶ Y) (g : Y ⟶ Y'),
      (totalToposHomEquiv F J K u0 X Y') (f ≫ g) =
        (totalToposHomEquiv F J K u0 X Y) f ≫ (pushforward F J K u0).map g) := by
  sorry

/-- The morphism of topoi `a : Sh(C_total) ⟶ Sh(D)` induced by the augmentation. -/
def totalTopos :
    MorphismOfTopoiIn K.toGrothendieck (topology F J) where
  inverseImageFunctor := LeftExactFunctor.of (inverseImage F J K u0)
  pushforward := pushforward F J K u0
  adjunction :=
    Adjunction.mkOfHomEquiv
      { homEquiv := totalToposHomEquiv F J K u0
        homEquiv_naturality_left_symm := (totalToposAdjunction_laws F J K u0).1
        homEquiv_naturality_right := (totalToposAdjunction_laws F J K u0).2 }

/-- Inverse image of the total morphism is the assembled sheaf-system inverse image. -/
theorem totalTopos_inverseImage :
    (totalTopos F J K u0)⁻¹ = inverseImage F J K u0 :=
  rfl

/-- Direct image of the total morphism is the equalizer functor `a_*`. -/
theorem totalTopos_pushforward :
    (totalTopos F J K u0).pushforward =
      pushforward F J K u0 :=
  rfl

/-- The augmentation arrow formula on the total category respects identities and composition. -/
private theorem totalFunctor_laws :
    (∀ X : Grothendieck F,
      (stageFunctor_compIso F J K u0 (Grothendieck.Hom.base (𝟙 X)).unop).inv.app X.fiber ≫
          (stageFunctor F u0 X.base.unop).map (Grothendieck.Hom.fiber (𝟙 X)) =
        𝟙 ((stageFunctor F u0 X.base.unop).obj X.fiber)) ∧
    (∀ {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z),
      (stageFunctor_compIso F J K u0 (f ≫ g).base.unop).inv.app X.fiber ≫
          (stageFunctor F u0 Z.base.unop).map (f ≫ g).fiber =
        ((stageFunctor_compIso F J K u0 f.base.unop).inv.app X.fiber ≫
          (stageFunctor F u0 Y.base.unop).map f.fiber) ≫
        ((stageFunctor_compIso F J K u0 g.base.unop).inv.app Y.fiber ≫
          (stageFunctor F u0 Z.base.unop).map g.fiber)) := by
  sorry

/-- The presenting functor `C_total ⥤ D` sending a degree-`n` object `U` to `u_n(U)`. -/
def totalFunctor : Grothendieck F ⥤ D where
  obj X := (stageFunctor F u0 X.base.unop).obj X.fiber
  map {X Y} f :=
    (stageFunctor_compIso F J K u0 f.base.unop).inv.app X.fiber ≫
      (stageFunctor F u0 Y.base.unop).map f.fiber
  map_id := (totalFunctor_laws F J K u0).1
  map_comp := (totalFunctor_laws F J K u0).2

/-- On a degree-`n` object `U`, the presenting functor is `u_n(U)`. -/
theorem totalFunctor_obj (n : SimplexCategory) (U : F.obj (op n)) :
    (totalFunctor F J K u0).obj ⟨op n, U⟩ =
      (stageFunctor F u0 n).obj U :=
  rfl

/-- The presenting functor of the total morphism is cocontinuous. -/
instance totalFunctor_isCocontinuous :
    (totalFunctor F J K u0).IsCocontinuous
      (topology F J) K.toGrothendieck :=
  sorry

variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]

/-- Restricting the assembled inverse image gives the stage inverse image naturally on sections. -/
private theorem restrictInverseImageIso_naturality
    (H : Sheaf K.toGrothendieck (Type w)) (n : SimplexCategory)
    {U V : (F.obj (op n))ᵒᵖ} (η : U ⟶ V) :
    (((restrictToDegree F J n).obj
      ((ofSheafSystem F J).obj ((inverseImageSystem F J K u0).obj H))).obj.map η ≫ 𝟙 _ =
      𝟙 _ ≫ ((stageTopos F J K u0 n)⁻¹.obj H).obj.map η) ∧
    (((stageTopos F J K u0 n)⁻¹.obj H).obj.map η ≫ 𝟙 _ =
      𝟙 _ ≫ ((restrictToDegree F J n).obj
      ((ofSheafSystem F J).obj ((inverseImageSystem F J K u0).obj H))).obj.map η) := by
  sorry

/-- Identity-on-sections identification of the degree-`n` restriction of `a⁻¹ H`
with `a_n⁻¹ H`. -/
private def restrictInverseImageIso (H : Sheaf K.toGrothendieck (Type w))
    (n : SimplexCategory) :
    (restrictToDegree F J n).obj
        ((ofSheafSystem F J).obj ((inverseImageSystem F J K u0).obj H)) ≅
      (stageTopos F J K u0 n)⁻¹.obj H where
  hom := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := fun _ _ η ↦
    (restrictInverseImageIso_naturality F J K u0 H n η).1 }
  inv := ObjectProperty.homMk
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ η ↦
        (restrictInverseImageIso_naturality F J K u0 H n η).2 }
  hom_inv_id := by ext U x; rfl
  inv_hom_id := by ext U x; rfl

/-- The comparison between total and stage inverse images is natural in the input sheaf. -/
private theorem totalTopos_comp_fiberMorphism_naturality (n : SimplexCategory)
    {G H : Sheaf K.toGrothendieck (Type w)} (α : G ⟶ H) :
    ((totalTopos F J K u0)⁻¹ ⋙ (fiberMorphism F J n)⁻¹).map α ≫
        ((sheafificationIso
          ((restrictToDegree F J n).obj
            ((ofSheafSystem F J).obj
              ((inverseImageSystem F J K u0).obj H)))).symm ≪≫
        restrictInverseImageIso F J K u0 H n).hom =
      ((sheafificationIso
          ((restrictToDegree F J n).obj
            ((ofSheafSystem F J).obj
              ((inverseImageSystem F J K u0).obj G)))).symm ≪≫
        restrictInverseImageIso F J K u0 G n).hom ≫ (stageTopos F J K u0 n)⁻¹.map α := by
  sorry

/-- Inverse-image form of `a ∘ g_n = a_n`. -/
def totalTopos_comp_fiberMorphism (n : SimplexCategory) :
    (totalTopos F J K u0)⁻¹ ⋙ (fiberMorphism F J n)⁻¹ ≅
      (stageTopos F J K u0 n)⁻¹ :=
  NatIso.ofComponents
    (fun H ↦
      (sheafificationIso
          ((restrictToDegree F J n).obj
            ((ofSheafSystem F J).obj
              ((inverseImageSystem F J K u0).obj H)))).symm ≪≫
        restrictInverseImageIso F J K u0 H n)
    (fun α ↦ totalTopos_comp_fiberMorphism_naturality F J K u0 n α)

end IsAugmentation

end CategoryTheory.Grothendieck
