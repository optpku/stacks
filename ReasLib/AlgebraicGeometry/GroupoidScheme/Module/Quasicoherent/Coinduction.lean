/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Forget
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.BaseChange

/-!
# Coinduction of quasi-coherent modules on a groupoid scheme

For a flat, quasi-compact, and quasi-separated source and target, this module
constructs the canonical equivariant structure on `s_* t^* F` and exhibits the
resulting coinduction functor as right adjoint to forgetting equivariance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

variable {S : Scheme.{u}}

/-- The first cartesian square of composable arrows, on underlying schemes. -/
theorem fstSndLeftIsPullback (G : GroupoidScheme S) :
    IsPullback (GroupoidScheme.composableFst G) (GroupoidScheme.composableSnd G)
      G.s.left G.t.left := sorry

/-- The composition-source cartesian square, on underlying schemes. -/
theorem compSndLeftIsPullback (G : GroupoidScheme S) :
    IsPullback (GroupoidScheme.compositionMap G) (GroupoidScheme.composableSnd G)
      G.s.left G.s.left := sorry

/-- The second projection from composable arrows is quasi-compact when the source is. -/
theorem composableSnd_quasiCompact (G : GroupoidScheme S) [QuasiCompact G.s.left] :
    QuasiCompact (GroupoidScheme.composableSnd G) := sorry

/-- The second projection from composable arrows is quasi-separated when the source is. -/
theorem composableSnd_quasiSeparated (G : GroupoidScheme S) [QuasiSeparated G.s.left] :
    QuasiSeparated (GroupoidScheme.composableSnd G) := sorry

/-- Pullback along `t` followed by the first projection agrees canonically with pullback
along `t` after composition. -/
noncomputable def targetComparisonIso (G : GroupoidScheme S) :
    Scheme.QCoh.pullback G.t.left ⋙
        Scheme.QCoh.pullback (GroupoidScheme.composableFst G) ≅
      Scheme.QCoh.pullback G.t.left ⋙
        Scheme.QCoh.pullback (GroupoidScheme.compositionMap G) :=
  (GroupoidScheme.pullbackCompIso (GroupoidScheme.composableFst G) G.t.left).symm ≪≫
    GroupoidScheme.pullbackEqIso (GroupoidScheme.compositionTargetLeft G).symm ≪≫
      GroupoidScheme.pullbackCompIso (GroupoidScheme.compositionMap G) G.t.left

/-- The first flat base-change component in the coinduction action. -/
noncomputable def coinductionFirstBaseChange (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    (Scheme.QCoh.pullback G.t.left).obj
        ((Scheme.QCoh.pushforward G.s.left).obj
          ((Scheme.QCoh.pullback G.t.left).obj F)) ⟶
      (@Scheme.QCoh.pushforward _ _ (GroupoidScheme.composableSnd G)
        (composableSnd_quasiCompact G) (composableSnd_quasiSeparated G)).obj
        ((Scheme.QCoh.pullback (GroupoidScheme.composableFst G)).obj
          ((Scheme.QCoh.pullback G.t.left).obj F)) :=
  -- Local instance justification (proof-local temporary data): base change needs second-projection quasi-compactness.
  letI : QuasiCompact (GroupoidScheme.composableSnd G) := composableSnd_quasiCompact G
  -- Local instance justification (proof-local temporary data): base change needs second-projection quasi-separatedness.
  letI : QuasiSeparated (GroupoidScheme.composableSnd G) := composableSnd_quasiSeparated G
  (Scheme.QCoh.BaseChange.map (fstSndLeftIsPullback G).toCommSq).app
    ((Scheme.QCoh.pullback G.t.left).obj F)

/-- The first base-change component in the coinduction action is invertible. -/
theorem coinductionFirstBaseChange_isIso (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    IsIso (coinductionFirstBaseChange G F) := sorry

/-- The second flat base-change component in the coinduction action. -/
noncomputable def coinductionSecondBaseChange (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    (Scheme.QCoh.pullback G.s.left).obj
        ((Scheme.QCoh.pushforward G.s.left).obj
          ((Scheme.QCoh.pullback G.t.left).obj F)) ⟶
      (@Scheme.QCoh.pushforward _ _ (GroupoidScheme.composableSnd G)
        (composableSnd_quasiCompact G) (composableSnd_quasiSeparated G)).obj
        ((Scheme.QCoh.pullback (GroupoidScheme.compositionMap G)).obj
          ((Scheme.QCoh.pullback G.t.left).obj F)) :=
  -- Local instance justification (proof-local temporary data): base change needs second-projection quasi-compactness.
  letI : QuasiCompact (GroupoidScheme.composableSnd G) := composableSnd_quasiCompact G
  -- Local instance justification (proof-local temporary data): base change needs second-projection quasi-separatedness.
  letI : QuasiSeparated (GroupoidScheme.composableSnd G) := composableSnd_quasiSeparated G
  (Scheme.QCoh.BaseChange.map (compSndLeftIsPullback G).toCommSq).app
    ((Scheme.QCoh.pullback G.t.left).obj F)

/-- The second base-change component in the coinduction action is invertible. -/
theorem coinductionSecondBaseChange_isIso (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    IsIso (coinductionSecondBaseChange G F) := sorry

/-- The canonical inverse of the second flat base-change component. -/
noncomputable def coinductionSecondBaseChangeInv (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    (@Scheme.QCoh.pushforward _ _ (GroupoidScheme.composableSnd G)
      (composableSnd_quasiCompact G) (composableSnd_quasiSeparated G)).obj
        ((Scheme.QCoh.pullback (GroupoidScheme.compositionMap G)).obj
          ((Scheme.QCoh.pullback G.t.left).obj F)) ⟶
      (Scheme.QCoh.pullback G.s.left).obj
        ((Scheme.QCoh.pushforward G.s.left).obj
          ((Scheme.QCoh.pullback G.t.left).obj F)) :=
  @inv _ _ _ _ (coinductionSecondBaseChange G F)
    (coinductionSecondBaseChange_isIso G F)

/-- The second base-change map followed by its canonical inverse is the identity. -/
theorem coinductionSecondBaseChange_hom_inv (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    coinductionSecondBaseChange G F ≫ coinductionSecondBaseChangeInv G F =
      𝟙 _ := sorry

/-- The canonical inverse followed by the second base-change map is the identity. -/
theorem coinductionSecondBaseChange_inv_hom (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    coinductionSecondBaseChangeInv G F ≫ coinductionSecondBaseChange G F =
      𝟙 _ := sorry

/-- The inverse of the second base-change map is uniquely determined by its right-inverse
equation. -/
theorem coinductionSecondBaseChangeInv_unique (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left)
    (i : (@Scheme.QCoh.pushforward _ _ (GroupoidScheme.composableSnd G)
          (composableSnd_quasiCompact G) (composableSnd_quasiSeparated G)).obj
          ((Scheme.QCoh.pullback (GroupoidScheme.compositionMap G)).obj
            ((Scheme.QCoh.pullback G.t.left).obj F)) ⟶
        (Scheme.QCoh.pullback G.s.left).obj
          ((Scheme.QCoh.pushforward G.s.left).obj
            ((Scheme.QCoh.pullback G.t.left).obj F)))
    (h : coinductionSecondBaseChange G F ≫ i = 𝟙 _) :
    i = coinductionSecondBaseChangeInv G F := sorry

/-- The canonical equivariance morphism on `s_* t^* F`, obtained from the two flat
base-change maps and the equality `c ≫ t = pr₀ ≫ t`. -/
noncomputable def coinductionAction (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    (Scheme.QCoh.pullback G.t.left).obj
        ((Scheme.QCoh.pushforward G.s.left).obj
          ((Scheme.QCoh.pullback G.t.left).obj F)) ⟶
      (Scheme.QCoh.pullback G.s.left).obj
        ((Scheme.QCoh.pushforward G.s.left).obj
          ((Scheme.QCoh.pullback G.t.left).obj F)) :=
  coinductionFirstBaseChange G F ≫
    (@Scheme.QCoh.pushforward _ _ (GroupoidScheme.composableSnd G)
      (composableSnd_quasiCompact G) (composableSnd_quasiSeparated G)).map
      ((targetComparisonIso G).hom.app F) ≫
        coinductionSecondBaseChangeInv G F

/-- The coinduction action is the first base-change map, followed by the target-comparison
map and the inverse of the second base-change map. -/
theorem coinductionAction_def (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    coinductionAction G F =
      coinductionFirstBaseChange G F ≫
        (@Scheme.QCoh.pushforward _ _ (GroupoidScheme.composableSnd G)
          (composableSnd_quasiCompact G) (composableSnd_quasiSeparated G)).map
          ((targetComparisonIso G).hom.app F) ≫
            coinductionSecondBaseChangeInv G F := sorry

/-- The coinduction action is a canonical isomorphism. -/
theorem coinductionAction_isIso (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) : IsIso (coinductionAction G F) := sorry

/-- The coinduction action satisfies the groupoid cocycle law. -/
theorem coinductionAction_cocycle (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    GroupoidScheme.Cocycle G
      ((Scheme.QCoh.pullback G.t.left ⋙ Scheme.QCoh.pushforward G.s.left).obj F)
      (coinductionAction G F) := sorry

/-- The coinduction action satisfies the groupoid unit law. -/
theorem coinductionAction_unit (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    GroupoidScheme.Unit G
      ((Scheme.QCoh.pullback G.t.left ⋙ Scheme.QCoh.pushforward G.s.left).obj F)
      (coinductionAction G F) := sorry

/-- The equivariant quasi-coherent module coinduced from `F`. -/
noncomputable def coinductionObj (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) : G.QCoh :=
  of ((Scheme.QCoh.pullback G.t.left ⋙ Scheme.QCoh.pushforward G.s.left).obj F)
    (coinductionAction G F) (coinductionAction_cocycle G F) (coinductionAction_unit G F)

/-- The underlying module of `coinductionObj G F` is `s_* t^* F`. -/
theorem coinductionObj_obj (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    (coinductionObj G F).obj =
      (Scheme.QCoh.pullback G.t.left ⋙ Scheme.QCoh.pushforward G.s.left).obj F := sorry

/-- The equivariance morphism of `coinductionObj G F` is `coinductionAction G F`. -/
theorem coinductionObj_action (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    (coinductionObj G F).action = coinductionAction G F := sorry

/-- The underlying map from an equivariant object into a coinduced object. -/
noncomputable def coinductionLiftUnderlying (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    {A : G.QCoh} {F : Scheme.QCoh G.U.left} (f : A.obj ⟶ F) :
    A.obj ⟶ (coinductionObj G F).obj :=
  (Scheme.QCoh.pullbackPushforwardAdjunction G.s.left).homEquiv A.obj
    ((Scheme.QCoh.pullback G.t.left).obj F)
      (actionInverse A ≫ (Scheme.QCoh.pullback G.t.left).map f)

/-- The map `coinductionLiftUnderlying` is compatible with equivariance. -/
theorem coinductionLift_compatibility (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    {A : G.QCoh} {F : Scheme.QCoh G.U.left} (f : A.obj ⟶ F) :
    (Scheme.QCoh.pullback G.t.left).map (coinductionLiftUnderlying G f) ≫
        (coinductionObj G F).action =
      A.action ≫
        (Scheme.QCoh.pullback G.s.left).map (coinductionLiftUnderlying G f) := sorry

/-- Lift an underlying module map to the canonical map into a coinduced object. -/
noncomputable def coinductionLift (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    {A : G.QCoh} {F : Scheme.QCoh G.U.left} (f : A.obj ⟶ F) :
    A ⟶ coinductionObj G F :=
  GroupoidScheme.System.Hom.of (coinductionLiftUnderlying G f)
    (coinductionLift_compatibility G f)

/-- Recover an underlying map from a map into a coinduced object by restricting along the
identity section of the groupoid. -/
noncomputable def coinductionDescend (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    {A : G.QCoh} {F : Scheme.QCoh G.U.left} (f : A ⟶ coinductionObj G F) :
    A.obj ⟶ F :=
  (GroupoidScheme.pullbackIdIso G.U.left).inv.app A.obj ≫
    (GroupoidScheme.pullbackEqIso (GroupoidScheme.identitySourceLeft G)).inv.app A.obj ≫
      (GroupoidScheme.pullbackCompIso G.e.left G.s.left).hom.app A.obj ≫
        (Scheme.QCoh.pullback G.e.left).map
          (((Scheme.QCoh.pullbackPushforwardAdjunction G.s.left).homEquiv A.obj
            ((Scheme.QCoh.pullback G.t.left).obj F)).symm (hom f)) ≫
          (GroupoidScheme.pullbackCompIso G.e.left G.t.left).inv.app F ≫
            (GroupoidScheme.pullbackEqIso (GroupoidScheme.identityTargetLeft G)).hom.app F ≫
              (GroupoidScheme.pullbackIdIso G.U.left).hom.app F

/-- Descending a lifted map returns the original underlying map. -/
theorem coinductionDescend_lift (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    {A : G.QCoh} {F : Scheme.QCoh G.U.left} (f : A.obj ⟶ F) :
    coinductionDescend G (coinductionLift G f) = f := sorry

/-- Lifting the descent of an equivariant map returns that map. -/
theorem coinductionLift_descend (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    {A : G.QCoh} {F : Scheme.QCoh G.U.left} (f : A ⟶ coinductionObj G F) :
    coinductionLift G (coinductionDescend G f) = f := sorry

/-- The canonical Hom equivalence defining the forgetful-coinduction adjunction. -/
noncomputable def forgetCoinductionHomEquiv (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (A : G.QCoh) (F : Scheme.QCoh G.U.left) :
    ((forget G).obj A ⟶ F) ≃ (A ⟶ coinductionObj G F) where
  toFun := coinductionLift G
  invFun := coinductionDescend G
  left_inv := coinductionDescend_lift G
  right_inv := coinductionLift_descend G

/-- The forward map of the coinduction Hom equivalence is `coinductionLift`. -/
theorem forgetCoinductionHomEquiv_apply (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    {A : G.QCoh} {F : Scheme.QCoh G.U.left} (f : (forget G).obj A ⟶ F) :
    forgetCoinductionHomEquiv G A F f = coinductionLift G f := sorry

/-- The inverse map of the coinduction Hom equivalence is `coinductionDescend`. -/
theorem forgetCoinductionHomEquiv_symm_apply (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    {A : G.QCoh} {F : Scheme.QCoh G.U.left} (f : A ⟶ coinductionObj G F) :
    (forgetCoinductionHomEquiv G A F).symm f = coinductionDescend G f := sorry

/-- The coinduction Hom equivalence is natural in the equivariant object. -/
theorem forgetCoinductionHomEquiv_naturality_left (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (A' A : G.QCoh) (F : Scheme.QCoh G.U.left) (f : A' ⟶ A)
    (g : (forget G).obj A ⟶ F) :
    forgetCoinductionHomEquiv G A' F ((forget G).map f ≫ g) =
      f ≫ forgetCoinductionHomEquiv G A F g := sorry

/-- Coinduction from ordinary quasi-coherent modules to equivariant ones. -/
noncomputable def coinduction (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left] :
    Scheme.QCoh G.U.left ⥤ G.QCoh :=
  Adjunction.rightAdjointOfEquiv (fun A F ↦ forgetCoinductionHomEquiv G A F)
    (forgetCoinductionHomEquiv_naturality_left G)

/-- The object assigned by coinduction is the explicit equivariant object `coinductionObj`. -/
theorem coinduction_obj (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    (coinduction G).obj F = coinductionObj G F := sorry

/-- The underlying module of a coinduced object is `s_* t^* F`. -/
theorem coinduction_obj_obj (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    ((coinduction G).obj F).obj =
      (Scheme.QCoh.pullback G.t.left ⋙ Scheme.QCoh.pushforward G.s.left).obj F := sorry

/-- The action on a coinduced object is the canonical base-change action. -/
theorem coinduction_action (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    (F : Scheme.QCoh G.U.left) :
    ((coinduction G).obj F).action = coinductionAction G F := sorry

/-- Coinduction maps a module morphism by the map determined by the Hom equivalence. -/
theorem coinduction_map (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left]
    {F F' : Scheme.QCoh G.U.left} (f : F ⟶ F') :
    (coinduction G).map f =
      forgetCoinductionHomEquiv G (coinductionObj G F) F'
        ((forgetCoinductionHomEquiv G (coinductionObj G F) F).symm (𝟙 _) ≫ f) := sorry

/-- The forgetful functor is left adjoint to explicit coinduction. -/
noncomputable def forgetCoinductionAdjunction (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left]
    [QuasiCompact G.s.left] [QuasiCompact G.t.left]
    [QuasiSeparated G.s.left] [QuasiSeparated G.t.left] :
    forget G ⊣ coinduction G :=
  Adjunction.adjunctionOfEquivRight
    (fun A F ↦ forgetCoinductionHomEquiv G A F)
    (forgetCoinductionHomEquiv_naturality_left G)

end AlgebraicGeometry.GroupoidScheme.QCoh
