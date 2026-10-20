module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import ReasLib.CategoryTheory.Sites.Simplicial.Augmentation
public import ReasLib.CategoryTheory.Sites.Simplicial.SheafComparison
public import ReasLib.CategoryTheory.Sites.Simplicial.Stage

/-!
# Augmentation morphisms of topoi, covariant case

An exact-site augmentation `u0` of a morphism diagram induces stage morphisms of
topoi `a_n` and a total morphism `a : Sh(C_total) ⟶ Sh(D)` whose inverse image is
the sheaf system of the functors `a_n⁻¹` and whose direct image is the equalizer of
the two coface maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`.
-/

-- Public constructions use private component maps without adding public implementation API.
set_option backward.privateInPublic true

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
include h_morphism
include h_aug



namespace IsAugmentation

/-- The common composite `u_n = u_φ ∘ u0` is an exact morphism of sites
`(D, K) ⟶ (C.obj n, J n)`. -/
instance stageFunctor_isExactMorphism (n : SimplexCategory) :
    IsExactMorphismOfSites K.toGrothendieck (J n).toGrothendieck
      (stageFunctor C u0 n) :=
  sorry

/-- Sheaf pullback along the stage functor `u_n` preserves finite limits. -/
instance stageFunctor_preservesFiniteLimits_sheafPullback
    (n : SimplexCategory) :
    PreservesFiniteLimits
      ((stageFunctor C u0 n).sheafPullback (Type w)
        K.toGrothendieck (J n).toGrothendieck) :=
  (stageFunctor_isExactMorphism C J K u0 n).preservesFiniteLimits_sheafPullback

/-- Identification `u_m ⋙ u_φ ≅ u_n` of presenting functors along a simplex operator. -/
def stageFunctor_compIso {m n : SimplexCategory} (φ : m ⟶ n) :
    stageFunctor C u0 m ⋙ (C.map φ).toFunctor ≅
      stageFunctor C u0 n :=
  Functor.associator u0 ((C.map (SimplexCategory.const ⦋0⦌ m 0)).toFunctor)
      (C.map φ).toFunctor ≪≫
    NatIso.hcomp (Iso.refl u0)
      (map_comp_toFunctor C (SimplexCategory.const ⦋0⦌ m 0) φ) ≪≫
    eqToIso (h_aug.map_eq (SimplexCategory.const ⦋0⦌ m 0 ≫ φ)
      (SimplexCategory.const ⦋0⦌ n 0))

/-- The morphism of topoi `a_n : Sh(C.obj n) ⟶ Sh(D)` presented by the common
composite `u_n`. -/
def stageTopos (n : SimplexCategory) :
    MorphismOfTopoiIn K.toGrothendieck (J n).toGrothendieck :=
  (stageFunctor C u0 n).morphismOfTopoiInOfContinuous
    K.toGrothendieck (J n).toGrothendieck

/-- Inverse image of `a_n` is sheaf pullback along `u_n`. -/
theorem stageTopos_inverseImage (n : SimplexCategory) :
    (stageTopos C J K u0 n)⁻¹ =
      (stageFunctor C u0 n).sheafPullback (Type w)
        K.toGrothendieck (J n).toGrothendieck :=
  rfl

/-- Direct image of `a_n` is continuous sheaf pushforward along `u_n`. -/
theorem stageTopos_pushforward (n : SimplexCategory) :
    (stageTopos C J K u0 n).pushforward =
      (stageFunctor C u0 n).sheafPushforwardContinuous (Type w)
        K.toGrothendieck (J n).toGrothendieck :=
  rfl

/-- Inverse-image form of `a_m ∘ f_φ = a_n`. -/
def stageTopos_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageTopos C J K u0 m)⁻¹ ⋙ (SimplicialSites.toposMap C J φ)⁻¹ ≅
      (stageTopos C J K u0 n)⁻¹ :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        ((stageFunctor C u0 m).sheafAdjunctionContinuous (Type w)
          K.toGrothendieck (J m).toGrothendieck)
        ((C.map φ).toFunctor.sheafAdjunctionContinuous (Type w)
          (J m).toGrothendieck (J n).toGrothendieck)).ofNatIsoRight
      (Functor.sheafPushforwardContinuousComp'
        (stageFunctor_compIso C J K u0 φ) (Type w)
        K.toGrothendieck (J m).toGrothendieck (J n).toGrothendieck))
    ((stageFunctor C u0 n).sheafAdjunctionContinuous (Type w)
      K.toGrothendieck (J n).toGrothendieck)

/-- Direct-image mate of `a_m ∘ f_φ = a_n`. -/
def stageTopos_pushforward_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (SimplicialSites.toposMap C J φ).pushforward ⋙ (stageTopos C J K u0 m).pushforward ≅
      (stageTopos C J K u0 n).pushforward :=
  MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
    (MorphismOfTopoiIn.comp (stageTopos C J K u0 m) (SimplicialSites.toposMap C J φ))
    (stageTopos C J K u0 n)
    (stageTopos_comp C J K u0 φ)

/-- Pushforward-form transition of the inverse-image sheaf system at a simplex operator. -/
private def inverseImageSystemMap (G : Sheaf K.toGrothendieck (Type w))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageTopos C J K u0 m)⁻¹.obj G ⟶
      (SimplicialSites.toposMap C J φ).pushforward.obj
        ((stageTopos C J K u0 n)⁻¹.obj G) :=
  ((SimplicialSites.toposMap C J φ).adjunction.homEquiv
      ((stageTopos C J K u0 m)⁻¹.obj G)
      ((stageTopos C J K u0 n)⁻¹.obj G))
    ((stageTopos_comp C J K u0 φ).hom.app G)

/-- The stagewise inverse-image transitions respect identities and composition. -/
private theorem inverseImageSystem_obj_laws
    (G : Sheaf K.toGrothendieck (Type w)) :
    (∀ n : SimplexCategory,
      inverseImageSystemMap C J K u0 G (𝟙 n) =
        (HasPushforwardFunctoriality.pushforwardIdIso
          (J := fun n ↦ (J n).toGrothendieck) (fHom := fun φ ↦ SimplicialSites.toposMap C J φ) n).inv.app
            ((stageTopos C J K u0 n)⁻¹.obj G)) ∧
    (∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      inverseImageSystemMap C J K u0 G (ψ ≫ φ) =
        inverseImageSystemMap C J K u0 G ψ ≫ (SimplicialSites.toposMap C J ψ).pushforward.map
          (inverseImageSystemMap C J K u0 G φ) ≫
          (HasPushforwardFunctoriality.pushforwardCompIso
            (J := fun n ↦ (J n).toGrothendieck) (fHom := fun φ ↦ SimplicialSites.toposMap C J φ)
            ψ φ).hom.app ((stageTopos C J K u0 n)⁻¹.obj G)) := by
  sorry

/-- Stage inverse images of a sheaf morphism commute with the system transitions. -/
private theorem inverseImageSystem_map_naturality
    {G H : Sheaf K.toGrothendieck (Type w)} (α : G ⟶ H)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    inverseImageSystemMap C J K u0 G φ ≫ (SimplicialSites.toposMap C J φ).pushforward.map
        ((stageTopos C J K u0 n)⁻¹.map α) =
      (stageTopos C J K u0 m)⁻¹.map α ≫
        inverseImageSystemMap C J K u0 H φ := by
  sorry

/-- The sheaf system whose stage sheaves are `a_n⁻¹ G` and whose transitions are the
identifications `f_φ⁻¹ a_m⁻¹ G ≅ a_n⁻¹ G`. -/
def inverseImageSystem :
    Sheaf K.toGrothendieck (Type w) ⥤
      SheafSystem (fun n ↦ (J n).toGrothendieck) (fun φ ↦ SimplicialSites.toposMap C J φ) where
  obj G :=
    SheafSystem.of (fun n ↦ (stageTopos C J K u0 n)⁻¹.obj G)
      (fun {m n} φ ↦ inverseImageSystemMap C J K u0 G φ) ((inverseImageSystem_obj_laws C J K u0 G).1)
      ((inverseImageSystem_obj_laws C J K u0 G).2)
  map {G H} α :=
    SheafSystem.homMk (fun n ↦ (stageTopos C J K u0 n)⁻¹.map α) (inverseImageSystem_map_naturality C J K u0 α)
  map_id := by
    intro G
    apply SheafSystem.Hom.ext
    intro n
    exact (stageTopos C J K u0 n)⁻¹.map_id G
  map_comp := by
    intro G H L α β
    apply SheafSystem.Hom.ext
    intro n
    exact (stageTopos C J K u0 n)⁻¹.map_comp α β

/-- The stage sheaf of `inverseImageSystem.obj G` at `n` is `a_n⁻¹ G`. -/
theorem inverseImageSystem_obj (G : Sheaf K.toGrothendieck (Type w))
    (n : SimplexCategory) :
    ((inverseImageSystem C J K u0).obj G).obj n =
      (stageTopos C J K u0 n)⁻¹.obj G :=
  rfl

/-- Inverse image `a⁻¹` of the total augmentation morphism, sending `G` to the sheaf
on `C_total` assembled from the system of the sheaves `a_n⁻¹ G`. -/
def inverseImage :
    Sheaf K.toGrothendieck (Type w) ⥤ Sheaf (topology C J) (Type w) :=
  inverseImageSystem C J K u0 ⋙ ofSheafSystem C J

/-- Inverse image of a sheaf `G` is `ofSheafSystem` of the system of the sheaves `a_n⁻¹ G`. -/
theorem inverseImage_obj (G : Sheaf K.toGrothendieck (Type w)) :
    (inverseImage C J K u0).obj G =
      (ofSheafSystem C J).obj ((inverseImageSystem C J K u0).obj G) :=
  rfl

/-- Inverse image `a⁻¹` preserves finite limits. -/
instance inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImage C J K u0) :=
  sorry

/-- The two maps `a_{0,*} F_0 ⇉ a_{1,*} F_1` induced by the coface operators `δ i`. -/
def pushforwardParallel (F : Sheaf (topology C J) (Type w)) (i : Fin 2) :
    (stageTopos C J K u0 ⦋0⦌).pushforward.obj
      (((toSheafSystem C J).obj F).obj ⦋0⦌) ⟶
      (stageTopos C J K u0 ⦋1⦌).pushforward.obj
        (((toSheafSystem C J).obj F).obj ⦋1⦌) :=
  (stageTopos C J K u0 ⦋0⦌).pushforward.map
      ((SimplicialSites.toposMap C J (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).adjunction.unit.app
        (((toSheafSystem C J).obj F).obj ⦋0⦌)) ≫
    (stageTopos C J K u0 ⦋0⦌).pushforward.map
      ((SimplicialSites.toposMap C J (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).pushforward.map
        (SheafSystem.mapInverseImage ((toSheafSystem C J).obj F)
          (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌))) ≫
    (stageTopos_pushforward_comp C J K u0
        (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).hom.app
      (((toSheafSystem C J).obj F).obj ⦋1⦌)

/-- The degree-zero direct image of a morphism preserves the two coface equalities. -/
private theorem pushforward_map_condition
    {F G : Sheaf (topology C J) (Type w)} (α : F ⟶ G) :
    (equalizer.ι (pushforwardParallel C J K u0 F 0)
          (pushforwardParallel C J K u0 F 1) ≫
        (stageTopos C J K u0 ⦋0⦌).pushforward.map
          (((toSheafSystem C J).map α).app ⦋0⦌)) ≫ pushforwardParallel C J K u0 G 0 =
      (equalizer.ι (pushforwardParallel C J K u0 F 0)
          (pushforwardParallel C J K u0 F 1) ≫
        (stageTopos C J K u0 ⦋0⦌).pushforward.map
          (((toSheafSystem C J).map α).app ⦋0⦌)) ≫ pushforwardParallel C J K u0 G 1 := by
  sorry

/-- Direct image `a_*`, sending a sheaf on `C_total` to the equalizer of
`a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
def pushforward :
    Sheaf (topology C J) (Type w) ⥤ Sheaf K.toGrothendieck (Type w) where
  obj F :=
    equalizer (pushforwardParallel C J K u0 F 0)
      (pushforwardParallel C J K u0 F 1)
  map {F G} α :=
    equalizer.lift
      (equalizer.ι (pushforwardParallel C J K u0 F 0)
          (pushforwardParallel C J K u0 F 1) ≫
        (stageTopos C J K u0 ⦋0⦌).pushforward.map
          (((toSheafSystem C J).map α).app ⦋0⦌))
      (pushforward_map_condition C J K u0 α)
  map_id := by
    intro F
    apply equalizer.hom_ext
    simp only [equalizer.lift_ι, Functor.map_id]
    change _ ≫ (stageTopos C J K u0 ⦋0⦌).pushforward.map (𝟙 _) = _
    simp
  map_comp := by
    intro F G L α β
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι]
    change _ ≫ (stageTopos C J K u0 ⦋0⦌).pushforward.map
        (((toSheafSystem C J).map (α ≫ β)).app ⦋0⦌) = _
    rw [(toSheafSystem C J).map_comp]
    change _ ≫ (stageTopos C J K u0 ⦋0⦌).pushforward.map
        ((((toSheafSystem C J).map α).app ⦋0⦌) ≫
          (((toSheafSystem C J).map β).app ⦋0⦌)) = _
    rw [Functor.map_comp]
    simp only [← Category.assoc, equalizer.lift_ι]

/-- The object `a_* F` is the equalizer of the two coface maps. -/
theorem pushforward_obj (F : Sheaf (topology C J) (Type w)) :
    (pushforward C J K u0).obj F =
      equalizer (pushforwardParallel C J K u0 F 0)
        (pushforwardParallel C J K u0 F 1) :=
  rfl

/-- The comparison `a_* F ⟶ a_{0,*} F_0`. -/
def pushforwardι (F : Sheaf (topology C J) (Type w)) :
    (pushforward C J K u0).obj F ⟶
      (stageTopos C J K u0 ⦋0⦌).pushforward.obj
        (((toSheafSystem C J).obj F).obj ⦋0⦌) :=
  equalizer.ι (pushforwardParallel C J K u0 F 0)
    (pushforwardParallel C J K u0 F 1)

/-- The fork presenting `a_* F` as equalizer of `a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
def pushforwardFork (F : Sheaf (topology C J) (Type w)) :
    Fork (pushforwardParallel C J K u0 F 0)
      (pushforwardParallel C J K u0 F 1) :=
  equalizer.fork (pushforwardParallel C J K u0 F 0)
    (pushforwardParallel C J K u0 F 1)

/-- The two coface maps coequalize `pushforwardι`. -/
theorem pushforwardFork_condition (F : Sheaf (topology C J) (Type w)) :
    pushforwardι C J K u0 F ≫
        pushforwardParallel C J K u0 F 0 =
      pushforwardι C J K u0 F ≫
        pushforwardParallel C J K u0 F 1 :=
  equalizer.condition _ _

/-- `a_* F` is the equalizer of the two maps `a_{0,*} F_0 ⇉ a_{1,*} F_1`. -/
def pushforwardFork_isLimit (F : Sheaf (topology C J) (Type w)) :
    IsLimit (pushforwardFork C J K u0 F) :=
  limit.isLimit
    (parallelPair (pushforwardParallel C J K u0 F 0)
      (pushforwardParallel C J K u0 F 1))

/-- The degree-zero adjoint of a total sheaf map satisfies the coface equality. -/
private theorem homEquivToFun_condition (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w))
    (α : (inverseImage C J K u0).obj G ⟶ F) :
    (((stageTopos C J K u0 ⦋0⦌).adjunction.homEquiv G
        (((toSheafSystem C J).obj F).obj ⦋0⦌))
      (((counitIso C J).inv.app ((inverseImageSystem C J K u0).obj G) ≫
          (toSheafSystem C J).map α).app ⦋0⦌)) ≫ pushforwardParallel C J K u0 F 0 =
      (((stageTopos C J K u0 ⦋0⦌).adjunction.homEquiv G
        (((toSheafSystem C J).obj F).obj ⦋0⦌))
      (((counitIso C J).inv.app ((inverseImageSystem C J K u0).obj G) ≫
          (toSheafSystem C J).map α).app ⦋0⦌)) ≫ pushforwardParallel C J K u0 F 1 := by
  sorry

/-- Degree-zero adjoint of a map `a⁻¹ G ⟶ F`, as a map `G ⟶ a_{0,*} F_0`. -/
private def homEquivToFun (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w))
    (α : (inverseImage C J K u0).obj G ⟶ F) :
    G ⟶ (pushforward C J K u0).obj F :=
  equalizer.lift
    (((stageTopos C J K u0 ⦋0⦌).adjunction.homEquiv G
        (((toSheafSystem C J).obj F).obj ⦋0⦌))
      (((counitIso C J).inv.app ((inverseImageSystem C J K u0).obj G) ≫
          (toSheafSystem C J).map α).app ⦋0⦌))
    (homEquivToFun_condition C J K u0 G F α)

/-- Stage-`n` component of the system map associated to a map `G ⟶ a_* F`. -/
private def homEquivInvFunApp (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w))
    (β : G ⟶ (pushforward C J K u0).obj F) (n : SimplexCategory) :
    (stageTopos C J K u0 n)⁻¹.obj G ⟶
      ((toSheafSystem C J).obj F).obj n :=
  (stageTopos_comp C J K u0 (SimplexCategory.const ⦋0⦌ n 0)).inv.app G ≫
    (SimplicialSites.toposMap C J (SimplexCategory.const ⦋0⦌ n 0)).inverseImage.map
      (((stageTopos C J K u0 ⦋0⦌).adjunction.homEquiv G
          (((toSheafSystem C J).obj F).obj ⦋0⦌)).symm
        (β ≫ pushforwardι C J K u0 F)) ≫
    SheafSystem.mapInverseImage ((toSheafSystem C J).obj F)
      (SimplexCategory.const ⦋0⦌ n 0)

/-- The components reconstructed from an equalizer map commute with simplex transitions. -/
private theorem homEquivInvFun_naturality (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w))
    (β : G ⟶ (pushforward C J K u0).obj F)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((inverseImageSystem C J K u0).obj G).map φ ≫
        (SimplicialSites.toposMap C J φ).pushforward.map
          (homEquivInvFunApp C J K u0 G F β n) =
      homEquivInvFunApp C J K u0 G F β m ≫
        ((toSheafSystem C J).obj F).map φ := by
  sorry

/-- The inverse adjunction map, assembling a morphism `a⁻¹ G ⟶ F` from `G ⟶ a_* F`. -/
private def homEquivInvFun (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w))
    (β : G ⟶ (pushforward C J K u0).obj F) :
    (inverseImage C J K u0).obj G ⟶ F :=
  (ofSheafSystem C J).map
      (SheafSystem.homMk (homEquivInvFunApp C J K u0 G F β) (homEquivInvFun_naturality C J K u0 G F β)) ≫
    (unitIso C J).inv.app F

/-- The explicit total adjunction maps are inverse to each other. -/
private theorem totalToposHomEquiv_laws (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w)) :
    Function.LeftInverse (homEquivInvFun C J K u0 G F) (homEquivToFun C J K u0 G F) ∧
      Function.RightInverse (homEquivInvFun C J K u0 G F) (homEquivToFun C J K u0 G F) := by
  sorry

/-- Hom-set equivalence `Hom(a⁻¹ G, F) ≃ Hom(G, a_* F)` of the total adjunction. -/
private def totalToposHomEquiv (G : Sheaf K.toGrothendieck (Type w))
    (F : Sheaf (topology C J) (Type w)) :
    ((inverseImage C J K u0).obj G ⟶ F) ≃
      (G ⟶ (pushforward C J K u0).obj F) where
  toFun := homEquivToFun C J K u0 G F
  invFun := homEquivInvFun C J K u0 G F
  left_inv := (totalToposHomEquiv_laws C J K u0 G F).1
  right_inv := (totalToposHomEquiv_laws C J K u0 G F).2

/-- The total Hom equivalence is natural in both sheaf arguments. -/
private theorem totalToposAdjunction_laws :
    (∀ {X' X : Sheaf K.toGrothendieck (Type w)}
      {Y : Sheaf (topology C J) (Type w)}
      (f : X' ⟶ X) (g : X ⟶ (pushforward C J K u0).obj Y),
      (totalToposHomEquiv C J K u0 X' Y).symm (f ≫ g) =
        (inverseImage C J K u0).map f ≫ (totalToposHomEquiv C J K u0 X Y).symm g) ∧
    (∀ {X : Sheaf K.toGrothendieck (Type w)}
      {Y Y' : Sheaf (topology C J) (Type w)}
      (f : (inverseImage C J K u0).obj X ⟶ Y) (g : Y ⟶ Y'),
      (totalToposHomEquiv C J K u0 X Y') (f ≫ g) =
        (totalToposHomEquiv C J K u0 X Y) f ≫ (pushforward C J K u0).map g) := by
  sorry

/-- The morphism of topoi `a : Sh(C_total) ⟶ Sh(D)` induced by the augmentation. -/
def totalTopos :
    MorphismOfTopoiIn K.toGrothendieck (topology C J) where
  inverseImageFunctor := LeftExactFunctor.of (inverseImage C J K u0)
  pushforward := pushforward C J K u0
  adjunction :=
    Adjunction.mkOfHomEquiv
      { homEquiv := totalToposHomEquiv C J K u0
        homEquiv_naturality_left_symm := (totalToposAdjunction_laws C J K u0).1
        homEquiv_naturality_right := (totalToposAdjunction_laws C J K u0).2 }

/-- Inverse image of the total morphism is the assembled sheaf-system inverse image. -/
theorem totalTopos_inverseImage :
    (totalTopos C J K u0)⁻¹ = inverseImage C J K u0 :=
  rfl

/-- Direct image of the total morphism is the equalizer functor `a_*`. -/
theorem totalTopos_pushforward :
    (totalTopos C J K u0).pushforward =
      pushforward C J K u0 :=
  rfl

variable [∀ n, (ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]

/-- Restricting the assembled inverse image gives the stage inverse image naturally on sections. -/
private theorem restrictInverseImageIso_naturality
    (G : Sheaf K.toGrothendieck (Type w)) (n : SimplexCategory)
    {U V : (C.obj n)ᵒᵖ} (η : U ⟶ V) :
    (((restrictToDegree C J n).obj
      ((ofSheafSystem C J).obj ((inverseImageSystem C J K u0).obj G))).obj.map η ≫ 𝟙 _ =
      𝟙 _ ≫ ((stageTopos C J K u0 n)⁻¹.obj G).obj.map η) ∧
    (((stageTopos C J K u0 n)⁻¹.obj G).obj.map η ≫ 𝟙 _ =
      𝟙 _ ≫ ((restrictToDegree C J n).obj
      ((ofSheafSystem C J).obj ((inverseImageSystem C J K u0).obj G))).obj.map η) := by
  sorry

/-- Identity-on-sections identification of the degree-`n` restriction of `a⁻¹ G`
with `a_n⁻¹ G`. -/
private def restrictInverseImageIso (G : Sheaf K.toGrothendieck (Type w))
    (n : SimplexCategory) :
    (restrictToDegree C J n).obj
        ((ofSheafSystem C J).obj ((inverseImageSystem C J K u0).obj G)) ≅
      (stageTopos C J K u0 n)⁻¹.obj G where
  hom := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := fun _ _ η ↦
    (restrictInverseImageIso_naturality C J K u0 G n η).1 }
  inv := ObjectProperty.homMk
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ η ↦
        (restrictInverseImageIso_naturality C J K u0 G n η).2 }
  hom_inv_id := by ext U x; rfl
  inv_hom_id := by ext U x; rfl

/-- The comparison between total and stage inverse images is natural in the input sheaf. -/
private theorem totalTopos_comp_ofStage_naturality (n : SimplexCategory)
    {G H : Sheaf K.toGrothendieck (Type w)} (α : G ⟶ H) :
    ((totalTopos C J K u0)⁻¹ ⋙ (ofStageMorphism C J n)⁻¹).map α ≫
        ((sheafificationIso
          ((restrictToDegree C J n).obj
            ((ofSheafSystem C J).obj
              ((inverseImageSystem C J K u0).obj H)))).symm ≪≫
        restrictInverseImageIso C J K u0 H n).hom =
      ((sheafificationIso
          ((restrictToDegree C J n).obj
            ((ofSheafSystem C J).obj
              ((inverseImageSystem C J K u0).obj G)))).symm ≪≫
        restrictInverseImageIso C J K u0 G n).hom ≫ (stageTopos C J K u0 n)⁻¹.map α := by
  sorry

/-- Inverse-image form of `a ∘ g_n = a_n`. -/
def totalTopos_comp_ofStage (n : SimplexCategory) :
    (totalTopos C J K u0)⁻¹ ⋙ (ofStageMorphism C J n)⁻¹ ≅
      (stageTopos C J K u0 n)⁻¹ :=
  NatIso.ofComponents
    (fun G ↦
      (sheafificationIso
          ((restrictToDegree C J n).obj
            ((ofSheafSystem C J).obj
              ((inverseImageSystem C J K u0).obj G)))).symm ≪≫
        restrictInverseImageIso C J K u0 G n)
    (fun α ↦ totalTopos_comp_ofStage_naturality C J K u0 n α)

end IsAugmentation

end CategoryTheory.SimplicialSites
