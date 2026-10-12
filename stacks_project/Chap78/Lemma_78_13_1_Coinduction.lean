/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Lemma_78_13_1_Forget
public import stacks_project.Chap67.Lemma_67_11_2_Pushforward
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Coinduction of quasi-coherent modules on a groupoid in algebraic spaces

For a flat, quasi-compact, and quasi-separated source and target, this module
constructs the canonical equivariant structure on `s_* t^* F` and exhibits the
resulting coinduction functor as right adjoint to forgetting equivariance.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The first cartesian square of composable arrows, on underlying algebraic spaces. -/
theorem fstSndLeftIsPullback (G : GroupoidAlgebraicSpace B) :
    IsPullback (composableFst G) (composableSnd G) G.s.left G.t.left := sorry

/-- The composition-source cartesian square, on underlying algebraic spaces. -/
theorem compSndLeftIsPullback (G : GroupoidAlgebraicSpace B) :
    IsPullback (compositionMap G) (composableSnd G) G.s.left G.s.left := sorry

/-- The second projection from composable arrows is quasi-compact when the source is. -/
instance composableSnd_quasiCompact (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.QuasiCompact G.s.left] :
    AlgebraicSpace.QuasiCompact (composableSnd G) := sorry

/-- The second projection from composable arrows is quasi-separated when the source is. -/
instance composableSnd_quasiSeparated (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.QuasiSeparated G.s.left] :
    AlgebraicSpace.QuasiSeparated (composableSnd G) := sorry

/-- Pullback along `t` followed by the first projection agrees canonically with pullback
along `t` after composition. -/
def coinductionTargetPullbackIso (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.QCoh.pullback G.t.left ⋙ AlgebraicSpace.QCoh.pullback (composableFst G) ≅
      AlgebraicSpace.QCoh.pullback G.t.left ⋙ AlgebraicSpace.QCoh.pullback (compositionMap G) :=
  (pullbackCompIso (composableFst G) G.t.left).symm ≪≫
    pullbackEqIso (compositionTargetLeft G).symm ≪≫
      pullbackCompIso (compositionMap G) G.t.left

/-- The forward component of `coinductionTargetPullbackIso` compares pullback along `pr₀ ≫ t`
with pullback along `c ≫ t`. -/
theorem coinductionTargetPullbackIso_hom (G : GroupoidAlgebraicSpace B)
    (F : AlgebraicSpace.QCoh G.U.left) :
    (coinductionTargetPullbackIso G).hom.app F =
      (pullbackCompIso (composableFst G) G.t.left).inv.app F ≫
        (pullbackEqIso (compositionTargetLeft G).symm).hom.app F ≫
          (pullbackCompIso (compositionMap G) G.t.left).hom.app F := sorry

/-- The inverse-oriented equivariance morphism obtained by reindexing the action along
groupoid inversion. -/
def actionInverse {G : GroupoidAlgebraicSpace B} (A : G.QCoh) :
    (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj ⟶
      (AlgebraicSpace.QCoh.pullback G.t.left).obj A.obj :=
  (pullbackEqIso (congrArg Over.Hom.left G.inverse_target)).inv.app A.obj ≫
    reindexAction G.t.left G.s.left G.i.left A.obj A.action ≫
      (pullbackEqIso (congrArg Over.Hom.left G.inverse_source)).hom.app A.obj

/-- The inversion-induced inverse followed by the action is the identity. -/
theorem actionInverse_comp_action {G : GroupoidAlgebraicSpace B} (A : G.QCoh) :
    actionInverse A ≫ A.action = 𝟙 _ := sorry

variable (G : GroupoidAlgebraicSpace B)
variable [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
variable [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
variable [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left]

/-- The underived mate component `t^* s_* t^* F ⟶ pr_{1,*} pr_0^* t^* F`. -/
def coinductionFirstBaseChangeHom (F : AlgebraicSpace.QCoh G.U.left) :
    ((AlgebraicSpace.QCoh.pullback G.t.left).obj
        ((AlgebraicSpace.QCoh.pushforward G.s.left).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F))).obj ⟶
      ((AlgebraicSpace.QCoh.pushforward (composableSnd G)).obj
        ((AlgebraicSpace.QCoh.pullback (composableFst G)).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F))).obj :=
  (AlgebraicSpace.Modules.pushforwardBaseChangeNatTrans (fstSndLeftIsPullback G)).app
    ((AlgebraicSpace.QCoh.pullback G.t.left).obj F).obj

/-- The first flat base-change component is an isomorphism on underlying modules. -/
instance isIso_coinductionFirstBaseChange (F : AlgebraicSpace.QCoh G.U.left) :
    IsIso (coinductionFirstBaseChangeHom G F) := sorry

/-- The identification `t^* s_* t^* F ≅ pr_{1,*} pr_0^* t^* F` from the first cartesian square. -/
def coinductionFirstBaseChangeIso (F : AlgebraicSpace.QCoh G.U.left) :
    (AlgebraicSpace.QCoh.pullback G.t.left).obj
        ((AlgebraicSpace.QCoh.pushforward G.s.left).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) ≅
      (AlgebraicSpace.QCoh.pushforward (composableSnd G)).obj
        ((AlgebraicSpace.QCoh.pullback (composableFst G)).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) :=
  (AlgebraicSpace.quasiCoherentModuleProperty G.R.left).isoMk
    (asIso (coinductionFirstBaseChangeHom G F))

/-- The first flat base-change component in the coinduction action. -/
def coinductionFirstBaseChange (F : AlgebraicSpace.QCoh G.U.left) :
    (AlgebraicSpace.QCoh.pullback G.t.left).obj
        ((AlgebraicSpace.QCoh.pushforward G.s.left).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) ⟶
      (AlgebraicSpace.QCoh.pushforward (composableSnd G)).obj
        ((AlgebraicSpace.QCoh.pullback (composableFst G)).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) :=
  (coinductionFirstBaseChangeIso G F).hom

/-- The forward component of `coinductionFirstBaseChangeIso` is `coinductionFirstBaseChange`. -/
theorem coinductionFirstBaseChangeIso_hom (F : AlgebraicSpace.QCoh G.U.left) :
    (coinductionFirstBaseChangeIso G F).hom = coinductionFirstBaseChange G F :=
  rfl

/-- The underived mate component `s^* s_* t^* F ⟶ pr_{1,*} c^* t^* F`. -/
def coinductionSecondBaseChangeHom (F : AlgebraicSpace.QCoh G.U.left) :
    ((AlgebraicSpace.QCoh.pullback G.s.left).obj
        ((AlgebraicSpace.QCoh.pushforward G.s.left).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F))).obj ⟶
      ((AlgebraicSpace.QCoh.pushforward (composableSnd G)).obj
        ((AlgebraicSpace.QCoh.pullback (compositionMap G)).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F))).obj :=
  (AlgebraicSpace.Modules.pushforwardBaseChangeNatTrans (compSndLeftIsPullback G)).app
    ((AlgebraicSpace.QCoh.pullback G.t.left).obj F).obj

/-- The second flat base-change component is an isomorphism on underlying modules. -/
instance isIso_coinductionSecondBaseChange (F : AlgebraicSpace.QCoh G.U.left) :
    IsIso (coinductionSecondBaseChangeHom G F) := sorry

/-- The identification `s^* s_* t^* F ≅ pr_{1,*} c^* t^* F` from the composition-source square. -/
def coinductionSecondBaseChangeIso (F : AlgebraicSpace.QCoh G.U.left) :
    (AlgebraicSpace.QCoh.pullback G.s.left).obj
        ((AlgebraicSpace.QCoh.pushforward G.s.left).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) ≅
      (AlgebraicSpace.QCoh.pushforward (composableSnd G)).obj
        ((AlgebraicSpace.QCoh.pullback (compositionMap G)).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) :=
  (AlgebraicSpace.quasiCoherentModuleProperty G.R.left).isoMk
    (asIso (coinductionSecondBaseChangeHom G F))

/-- The second flat base-change component in the coinduction action. -/
def coinductionSecondBaseChange (F : AlgebraicSpace.QCoh G.U.left) :
    (AlgebraicSpace.QCoh.pullback G.s.left).obj
        ((AlgebraicSpace.QCoh.pushforward G.s.left).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) ⟶
      (AlgebraicSpace.QCoh.pushforward (composableSnd G)).obj
        ((AlgebraicSpace.QCoh.pullback (compositionMap G)).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) :=
  (coinductionSecondBaseChangeIso G F).hom

/-- The forward component of `coinductionSecondBaseChangeIso` is `coinductionSecondBaseChange`. -/
theorem coinductionSecondBaseChangeIso_hom (F : AlgebraicSpace.QCoh G.U.left) :
    (coinductionSecondBaseChangeIso G F).hom = coinductionSecondBaseChange G F :=
  rfl

/-- The canonical equivariance morphism on `s_* t^* F`, obtained from the two flat
base-change maps and the equality `c ≫ t = pr₀ ≫ t`. -/
def coinductionAction (F : AlgebraicSpace.QCoh G.U.left) :
    (AlgebraicSpace.QCoh.pullback G.t.left).obj
        ((AlgebraicSpace.QCoh.pushforward G.s.left).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) ⟶
      (AlgebraicSpace.QCoh.pullback G.s.left).obj
        ((AlgebraicSpace.QCoh.pushforward G.s.left).obj
          ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)) :=
  coinductionFirstBaseChange G F ≫
    (AlgebraicSpace.QCoh.pushforward (composableSnd G)).map
      ((coinductionTargetPullbackIso G).hom.app F) ≫
      (coinductionSecondBaseChangeIso G F).inv

/-- The coinduction action is the first base-change map, followed by the target-comparison
map and the inverse of the second base-change map. -/
theorem coinductionAction_def (F : AlgebraicSpace.QCoh G.U.left) :
    coinductionAction G F =
      coinductionFirstBaseChange G F ≫
        (AlgebraicSpace.QCoh.pushforward (composableSnd G)).map
          ((coinductionTargetPullbackIso G).hom.app F) ≫
          (coinductionSecondBaseChangeIso G F).inv :=
  rfl

/-- The coinduction action is a canonical isomorphism. -/
theorem coinductionAction_isIso (F : AlgebraicSpace.QCoh G.U.left) :
    IsIso (coinductionAction G F) := sorry

/-- The coinduction action satisfies the groupoid cocycle law. -/
theorem coinductionAction_cocycle (F : AlgebraicSpace.QCoh G.U.left) :
    Cocycle G ((AlgebraicSpace.QCoh.pullback G.t.left ⋙
        AlgebraicSpace.QCoh.pushforward G.s.left).obj F)
      (coinductionAction G F) := sorry

/-- The coinduction action satisfies the groupoid unit law. -/
theorem coinductionAction_unit (F : AlgebraicSpace.QCoh G.U.left) :
    Unit G ((AlgebraicSpace.QCoh.pullback G.t.left ⋙
        AlgebraicSpace.QCoh.pushforward G.s.left).obj F)
      (coinductionAction G F) := sorry

/-- The equivariant quasi-coherent module coinduced from `F`. -/
def coinductionObj (F : AlgebraicSpace.QCoh G.U.left) : G.QCoh :=
  of ((AlgebraicSpace.QCoh.pullback G.t.left ⋙ AlgebraicSpace.QCoh.pushforward G.s.left).obj F)
    (coinductionAction G F) (coinductionAction_cocycle G F) (coinductionAction_unit G F)

/-- The underlying module of `coinductionObj G F` is `s_* t^* F`. -/
theorem coinductionObj_obj (F : AlgebraicSpace.QCoh G.U.left) :
    (coinductionObj G F).obj =
      (AlgebraicSpace.QCoh.pullback G.t.left ⋙ AlgebraicSpace.QCoh.pushforward G.s.left).obj F :=
  rfl

/-- The equivariance morphism of `coinductionObj G F` is `coinductionAction G F`. -/
theorem coinductionObj_action (F : AlgebraicSpace.QCoh G.U.left) :
    (coinductionObj G F).action = coinductionAction G F :=
  rfl

/-- Pushforward of `s_* t^* φ` remains compatible with the coinduction actions. -/
theorem coinductionMap_compatibility {F F' : AlgebraicSpace.QCoh G.U.left} (φ : F ⟶ F') :
    (AlgebraicSpace.QCoh.pullback G.t.left).map
          ((AlgebraicSpace.QCoh.pullback G.t.left ⋙
              AlgebraicSpace.QCoh.pushforward G.s.left).map φ) ≫
        (coinductionObj G F').action =
      (coinductionObj G F).action ≫
        (AlgebraicSpace.QCoh.pullback G.s.left).map
          ((AlgebraicSpace.QCoh.pullback G.t.left ⋙
              AlgebraicSpace.QCoh.pushforward G.s.left).map φ) := sorry

/-- Coinduction of an ordinary quasi-coherent morphism, packaged as an equivariant map. -/
def coinductionMap {F F' : AlgebraicSpace.QCoh G.U.left} (φ : F ⟶ F') :
    coinductionObj G F ⟶ coinductionObj G F' :=
  System.Hom.of
    ((AlgebraicSpace.QCoh.pullback G.t.left ⋙ AlgebraicSpace.QCoh.pushforward G.s.left).map φ)
    (coinductionMap_compatibility G φ)

/-- Coinduction preserves identity morphisms. -/
theorem coinductionMap_id (F : AlgebraicSpace.QCoh G.U.left) :
    coinductionMap G (𝟙 F) = 𝟙 (coinductionObj G F) := sorry

/-- Coinduction preserves composition. -/
theorem coinductionMap_comp {F F' F'' : AlgebraicSpace.QCoh G.U.left}
    (φ : F ⟶ F') (ψ : F' ⟶ F'') :
    coinductionMap G (φ ≫ ψ) = coinductionMap G φ ≫ coinductionMap G ψ := sorry

/-- Coinduction from ordinary quasi-coherent modules to equivariant ones. -/
def coinduction : AlgebraicSpace.QCoh G.U.left ⥤ G.QCoh where
  obj := coinductionObj G
  map := coinductionMap G
  map_id := coinductionMap_id G
  map_comp := coinductionMap_comp G

/-- The object assigned by coinduction is the explicit equivariant object `coinductionObj`. -/
theorem coinduction_obj (F : AlgebraicSpace.QCoh G.U.left) :
    (coinduction G).obj F = coinductionObj G F :=
  rfl

/-- The underlying module of a coinduced object is `s_* t^* F`. -/
theorem coinduction_obj_obj (F : AlgebraicSpace.QCoh G.U.left) :
    ((coinduction G).obj F).obj =
      (AlgebraicSpace.QCoh.pullback G.t.left ⋙ AlgebraicSpace.QCoh.pushforward G.s.left).obj F :=
  rfl

/-- The action on a coinduced object is the canonical base-change action. -/
theorem coinduction_action (F : AlgebraicSpace.QCoh G.U.left) :
    ((coinduction G).obj F).action = coinductionAction G F :=
  rfl

/-- The underlying map of a coinduced morphism is ordinary `s_* t^* φ`. -/
theorem coinduction_map {F F' : AlgebraicSpace.QCoh G.U.left} (φ : F ⟶ F') :
    hom ((coinduction G).map φ) =
      (AlgebraicSpace.QCoh.pullback G.t.left ⋙ AlgebraicSpace.QCoh.pushforward G.s.left).map φ :=
  rfl

/-- The underlying map from an equivariant object into a coinduced object. -/
def coinductionLiftUnderlying {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left}
    (f : A.obj ⟶ F) : A.obj ⟶ (coinductionObj G F).obj :=
  (AlgebraicSpace.quasiCoherentModuleProperty G.U.left).homMk
    ((AlgebraicSpace.Modules.pullbackPushforwardAdjunction G.s.left).homEquiv A.obj.obj
      ((AlgebraicSpace.Modules.pullback G.t.left).obj F.obj)
      ((actionInverse A ≫ (AlgebraicSpace.QCoh.pullback G.t.left).map f).hom))

/-- The map `coinductionLiftUnderlying` is compatible with equivariance. -/
theorem coinductionLift_compatibility {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left}
    (f : A.obj ⟶ F) :
    (AlgebraicSpace.QCoh.pullback G.t.left).map (coinductionLiftUnderlying G f) ≫
        (coinductionObj G F).action =
      A.action ≫
        (AlgebraicSpace.QCoh.pullback G.s.left).map (coinductionLiftUnderlying G f) := sorry

/-- Lift an underlying module map to the canonical map into a coinduced object. -/
def coinductionLift {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left} (f : A.obj ⟶ F) :
    A ⟶ coinductionObj G F :=
  System.Hom.of (coinductionLiftUnderlying G f) (coinductionLift_compatibility G f)

/-- The adjunct of an equivariant map into a coinduced object, as a map `s^* A ⟶ t^* F`. -/
def coinductionDescendAdjunct {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left}
    (f : A ⟶ coinductionObj G F) :
    (AlgebraicSpace.QCoh.pullback G.s.left).obj A.obj ⟶
      (AlgebraicSpace.QCoh.pullback G.t.left).obj F :=
  (AlgebraicSpace.quasiCoherentModuleProperty G.R.left).homMk
    (((AlgebraicSpace.Modules.pullbackPushforwardAdjunction G.s.left).homEquiv
        A.obj.obj ((AlgebraicSpace.Modules.pullback G.t.left).obj F.obj)).symm (hom f).hom)

/-- The underlying module morphism of `coinductionDescendAdjunct` is the module-level adjunct. -/
theorem coinductionDescendAdjunct_hom {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left}
    (f : A ⟶ coinductionObj G F) :
    (coinductionDescendAdjunct G f).hom =
      (((AlgebraicSpace.Modules.pullbackPushforwardAdjunction G.s.left).homEquiv
          A.obj.obj ((AlgebraicSpace.Modules.pullback G.t.left).obj F.obj)).symm (hom f).hom) :=
  rfl

/-- Recover an underlying map from a map into a coinduced object by restricting along the
identity section of the groupoid. -/
def coinductionDescend {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left}
    (f : A ⟶ coinductionObj G F) : A.obj ⟶ F :=
  (pullbackIdIso G.U.left).inv.app A.obj ≫
    (pullbackEqIso (identitySourceLeft G)).inv.app A.obj ≫
      (pullbackCompIso G.e.left G.s.left).hom.app A.obj ≫
        (AlgebraicSpace.QCoh.pullback G.e.left).map (coinductionDescendAdjunct G f) ≫
          (pullbackCompIso G.e.left G.t.left).inv.app F ≫
            (pullbackEqIso (identityTargetLeft G)).hom.app F ≫
              (pullbackIdIso G.U.left).hom.app F

/-- Descending a lifted map returns the original underlying map. -/
theorem coinductionDescend_lift {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left}
    (f : A.obj ⟶ F) : coinductionDescend G (coinductionLift G f) = f := sorry

/-- Lifting the descent of an equivariant map returns that map. -/
theorem coinductionLift_descend {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left}
    (f : A ⟶ coinductionObj G F) : coinductionLift G (coinductionDescend G f) = f := sorry

/-- The canonical Hom equivalence defining the forgetful-coinduction adjunction. -/
def forgetCoinductionHomEquiv (A : G.QCoh) (F : AlgebraicSpace.QCoh G.U.left) :
    ((forget G).obj A ⟶ F) ≃ (A ⟶ coinductionObj G F) where
  toFun := coinductionLift G
  invFun := coinductionDescend G
  left_inv := coinductionDescend_lift G
  right_inv := coinductionLift_descend G

/-- The forward map of the coinduction Hom equivalence is `coinductionLift`. -/
theorem forgetCoinductionHomEquiv_apply {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left}
    (f : (forget G).obj A ⟶ F) :
    forgetCoinductionHomEquiv G A F f = coinductionLift G f :=
  rfl

/-- The inverse map of the coinduction Hom equivalence is `coinductionDescend`. -/
theorem forgetCoinductionHomEquiv_symm_apply {A : G.QCoh} {F : AlgebraicSpace.QCoh G.U.left}
    (f : A ⟶ coinductionObj G F) :
    (forgetCoinductionHomEquiv G A F).symm f = coinductionDescend G f :=
  rfl

/-- The coinduction Hom equivalence is natural in the equivariant object. -/
theorem forgetCoinductionHomEquiv_naturality_left (A' A : G.QCoh)
    (F : AlgebraicSpace.QCoh G.U.left) (f : A' ⟶ A) (g : (forget G).obj A ⟶ F) :
    forgetCoinductionHomEquiv G A' F ((forget G).map f ≫ g) =
      f ≫ forgetCoinductionHomEquiv G A F g := sorry

/-- The coinduction Hom equivalence is natural in the ordinary quasi-coherent module. -/
theorem forgetCoinductionHomEquiv_naturality_right {A : G.QCoh}
    {F F' : AlgebraicSpace.QCoh G.U.left} (f : (forget G).obj A ⟶ F) (g : F ⟶ F') :
    forgetCoinductionHomEquiv G A F' (f ≫ g) =
      forgetCoinductionHomEquiv G A F f ≫ (coinduction G).map g := sorry

/-- The inverse coinduction Hom equivalence is natural in the equivariant object. -/
theorem forgetCoinductionHomEquiv_naturality_left_symm {A' A : G.QCoh}
    {F : AlgebraicSpace.QCoh G.U.left} (f : A' ⟶ A) (g : A ⟶ (coinduction G).obj F) :
    (forgetCoinductionHomEquiv G A' F).symm (f ≫ g) =
      (forget G).map f ≫ (forgetCoinductionHomEquiv G A F).symm g := sorry

/-- The forgetful functor is left adjoint to explicit coinduction. -/
def forgetCoinductionAdjunction : forget G ⊣ coinduction G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A F ↦ forgetCoinductionHomEquiv G A F
      homEquiv_naturality_left_symm := fun f g ↦
        forgetCoinductionHomEquiv_naturality_left_symm G f g
      homEquiv_naturality_right := fun f g ↦
        forgetCoinductionHomEquiv_naturality_right G f g }

/-- The Hom equivalence of the forgetful-coinduction adjunction is `forgetCoinductionHomEquiv`. -/
theorem forgetCoinductionAdjunction_homEquiv (A : G.QCoh) (F : AlgebraicSpace.QCoh G.U.left) :
    (forgetCoinductionAdjunction G).homEquiv A F = forgetCoinductionHomEquiv G A F :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
