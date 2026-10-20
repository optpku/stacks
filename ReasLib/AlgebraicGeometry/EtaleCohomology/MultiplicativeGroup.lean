module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor
public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace
public import ReasLib.AlgebraicGeometry.RootsOfUnity.GroupScheme
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Monoidal.Grp.MulBy
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import ReasLib.CategoryTheory.Sites.Torsor.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Kummer

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.AssociatedModule
open Opposite
open CartesianMonoidalCategory
noncomputable section

universe u

namespace AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup

open AlgebraicGeometry.MultiplicativeGroup
open AlgebraicGeometry.RootsOfUnity
open AlgebraicGeometry.GroupScheme
open AlgebraicGeometry.ProjectiveLine
open AlgebraicGeometry.Scheme

/-- Scalar restriction `ULift ℤ → k`. -/
def uliftIntRingHom (k : Type u) [CommRing k] : ULift.{u} ℤ →+* k :=
  (algebraMap ℤ k).comp ULift.ringEquiv.toRingHom

/-- The canonical algebra structure obtained by restricting integral scalars. -/
instance uliftIntAlgebra (k : Type u) [CommRing k] : Algebra (ULift.{u} ℤ) k :=
  (uliftIntRingHom k).toAlgebra

/-- Laurent polynomials over lifted integers carry their coefficient algebra structure. -/
instance laurentOverULiftInt : Algebra (ULift.{u} ℤ) (LaurentPolynomial (ULift.{u} ℤ)) :=
  RingHom.toAlgebra LaurentPolynomial.C

/-- The multiplicative group scheme over a field, as the defining fibre product. -/
abbrev Gm (k : Type u) [Field k] : Scheme.{u} :=
  pullback overInt.hom (specULiftZIsTerminal.from (Spec (CommRingCat.of k)))

/-- The integral multiplicative group scheme. -/
abbrev GmInt : Scheme.{u} :=
  (𝔾ₘ : CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ))))).X.left

/-- The Laurent-polynomial model of the punctured affine line over `k`. -/
abbrev puncturedAffineLine (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (LaurentPolynomial k))

/-- The open `D₊(X) ∩ D₊(Y)` on `ℙ¹_k`, i.e. the complement of `{0, ∞}`. -/
abbrev puncturedProjectiveLine (k : Type u) [Field k] : Scheme.{u} :=
  (chartX k ⊓ chartY k).toScheme

/-- The small étale Kummer coefficient sheaf `μₙ` on a scheme. -/
abbrev rootsSheaf (S : Scheme.{u}) (n : ℕ) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  CategoryTheory.Sheaf.rootsOfUnityAddSheaf (smallCommStructureSheaf .etale S) n

/-- The constant étale sheaf of coefficients `ZMod n`. -/
abbrev constantZModSheaf (S : Scheme.{u}) (n : ℕ) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

/-- Degree-one étale cohomology of `𝔾ₘ,k` with coefficients in `μₙ`. -/
abbrev h1Roots (k : Type u) [Field k] (n : ℕ)
    [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})] :
    Type (u + 1) :=
  (rootsSheaf (Gm k) n).H 1

/-- Degree-one étale cohomology of `𝔾ₘ,k` with constant `ZMod n` coefficients. -/
abbrev h1Constant (k : Type u) [Field k] (n : ℕ)
    [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})] :
    Type (u + 1) :=
  (constantZModSheaf (Gm k) n).H 1

/-- The `n`-power map `x ↦ x^n` on the integral multiplicative group. -/
def powerMap (n : ℕ) : GmInt ⟶ GmInt :=
  (GrpObj.mulBy
      (𝔾ₘ : CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ))))).X n).left

/-- The integral Kummer cover as an object of `Over 𝔾ₘ,ℤ`. -/
def powerMapOver (n : ℕ) : Over GmInt :=
  Over.mk (powerMap n)

/-- The underlying scheme of integral `𝔾ₘ` is `overInt.left`. -/
theorem gmInt_eq_overInt_left :
    GmInt = overInt.left :=
  congrArg Over.left AlgebraicGeometry.MultiplicativeGroup.groupScheme_X

/-- Multiplication by roots of unity acts on the integral power cover. -/
def powerMapTorsor (n : ℕ) [NeZero n] :
    Mod (Over GmInt) (μₙ n over GmInt).X where
  X := powerMapOver n
  mod :=
    { smul :=
        let product := MonoidalCategory.tensorObj (μₙ n over GmInt).X (powerMapOver n)
        let root := RootsOfUnity.BaseChange.homMulEquiv n GmInt product
          (fst (μₙ n over GmInt).X (powerMapOver n))
        let coordinate := AlgebraicGeometry.MultiplicativeGroup.homEquiv product.left
          ((snd (μₙ n over GmInt).X (powerMapOver n)).left ≫
            eqToHom gmInt_eq_overInt_left)
        Over.homMk
          ((AlgebraicGeometry.MultiplicativeGroup.homEquiv product.left).symm
            (root.val * coordinate) ≫ eqToHom gmInt_eq_overInt_left.symm) sorry
      one_smul := sorry
      mul_smul := sorry }

/-- The integral power cover is an fppf torsor under the roots-of-unity group scheme. -/
theorem powerMap_isTorsor (n : ℕ) [NeZero n] :
    IsTorsorFor (μₙ n over GmInt).toGrp (powerMapTorsor n)
      StandardTopology.fppf.precoverage := sorry

/-- The invertible generator `T` of `LaurentPolynomial R`. -/
def laurentTUnit (R : Type u) [CommRing R] : (LaurentPolynomial R)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := sorry
  inv_val := sorry

/-- Ring hom `LaurentPolynomial (ULift ℤ) → LaurentPolynomial k` sending `T` to `T`. -/
def laurentMapScalars (k : Type u) [CommRing k] [Algebra (ULift.{u} ℤ) k] :
    LaurentPolynomial (ULift.{u} ℤ) →+* LaurentPolynomial k :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (algebraMap (ULift.{u} ℤ) k))
    (laurentTUnit k)

/-- Global sections of `overInt.left` identify with Laurent polynomials after `overInt_left`. -/
def overIntLeftRingHom (k : Type u) [Field k] :
    LaurentPolynomial (ULift.{u} ℤ) →+* Γ(Gm k, ⊤) :=
  CommRingCat.Hom.hom
    ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)))).inv ≫
      (pullback.fst overInt.hom
          (specULiftZIsTerminal.from (Spec (CommRingCat.of k))) ≫
        eqToHom AlgebraicGeometry.MultiplicativeGroup.overInt_left).appTop)

/-- The tautological coordinate unit pulled back from integral `𝔾ₘ`. -/
def tautologicalCoordinateUnit (k : Type u) [Field k] : Γ(Gm k, ⊤)ˣ :=
  Units.map (overIntLeftRingHom k) coordinateUnit

/-- Evaluation of Laurent polynomials over `k` on global functions of `𝔾ₘ,k`. -/
def tautologicalLaurentEval (k : Type u) [Field k] :
    LaurentPolynomial k →+* Γ(Gm k, ⊤) :=
  LaurentPolynomial.eval₂
    (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (pullback.snd overInt.hom
          (specULiftZIsTerminal.from (Spec (CommRingCat.of k)))).appTop))
    (tautologicalCoordinateUnit k)

/-- Compatibility of the two maps used to invert the punctured-affine identification. -/
theorem puncturedAffineLine_lift_w (k : Type u) [Field k] :
    Spec.map (CommRingCat.ofHom (laurentMapScalars k)) ≫
        eqToHom AlgebraicGeometry.MultiplicativeGroup.overInt_left.symm ≫
        overInt.hom =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* LaurentPolynomial k)) ≫
        specULiftZIsTerminal.from (Spec (CommRingCat.of k)) := sorry

/-- `𝔾ₘ,k` is identified with the Laurent model of the punctured affine line. -/
def multiplicativeGroup_eq_puncturedAffineLine (k : Type u) [Field k] :
    Gm k ≅ puncturedAffineLine k where
  hom :=
    (Gm k).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (tautologicalLaurentEval k))
  inv :=
    pullback.lift
      (Spec.map (CommRingCat.ofHom (laurentMapScalars k)) ≫
        eqToHom AlgebraicGeometry.MultiplicativeGroup.overInt_left.symm)
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* LaurentPolynomial k)))
      (puncturedAffineLine_lift_w k)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The projection `𝔾ₘ,k ⟶ 𝔾ₘ,ℤ` of the defining fibre product. -/
def gmToInt (k : Type u) [Field k] : Gm k ⟶ GmInt :=
  pullback.fst overInt.hom
      (specULiftZIsTerminal.from (Spec (CommRingCat.of k))) ≫
    eqToHom gmInt_eq_overInt_left.symm

/-- The two projections of `𝔾ₘ,k'` are compatible with `Spec k' ⟶ Spec k`. -/
theorem gmMap_lift_w (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    pullback.fst overInt.hom (specULiftZIsTerminal.from (Spec (CommRingCat.of k'))) ≫
        overInt.hom =
      (pullback.snd overInt.hom (specULiftZIsTerminal.from (Spec (CommRingCat.of k'))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k k'))) ≫
        specULiftZIsTerminal.from (Spec (CommRingCat.of k)) := sorry

/-- The morphism `𝔾ₘ,k' ⟶ 𝔾ₘ,k` induced by `Spec k' ⟶ Spec k`. -/
def gmMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Gm k' ⟶ Gm k :=
  pullback.lift
    (pullback.fst overInt.hom
      (specULiftZIsTerminal.from (Spec (CommRingCat.of k'))))
    (pullback.snd overInt.hom
        (specULiftZIsTerminal.from (Spec (CommRingCat.of k'))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k k')))
    (gmMap_lift_w k k')

/-- The tautological multiplicative coordinate gives the first projective affine chart map. -/
def multiplicativeGroup_to_projectiveLine (k : Type u) [Field k] :
    Gm k ⟶ scheme k :=
  AffineSpace.homOfVector
    (pullback.snd overInt.hom (specULiftZIsTerminal.from (Spec (CommRingCat.of k))))
    (fun _ ↦ (tautologicalCoordinateUnit k).val) ≫
      (chartXIso k).inv ≫ (chartX k).ι

/-- The tautological coordinate map lands in the intersection of the projective charts. -/
theorem multiplicativeGroup_to_projectiveLine_mem (k : Type u) [Field k] :
    Set.range (multiplicativeGroup_to_projectiveLine k).base ≤
      Set.range (chartX k ⊓ chartY k).ι.base := sorry

/-- The coordinates `Y/X` and `X/Y` on the punctured projective line are reciprocal units. -/
def puncturedProjectiveLineCoordinateUnit (k : Type u) [Field k] :
    Γ(puncturedProjectiveLine k, ⊤)ˣ where
  val := ((scheme k).homOfLE (U := chartX k ⊓ chartY k) inf_le_left ≫
    (chartXIso k).hom).appTop.hom
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up (0 : Fin 1)))
  inv := ((scheme k).homOfLE (U := chartX k ⊓ chartY k) inf_le_right ≫
    (chartYIso k).hom).appTop.hom
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up (0 : Fin 1)))
  val_inv := sorry
  inv_val := sorry

/-- The invertible chart coordinate represents a morphism to the integral multiplicative group. -/
def puncturedProjectiveLineToIntegral (k : Type u) [Field k] :
    puncturedProjectiveLine k ⟶ GmInt :=
  (AlgebraicGeometry.MultiplicativeGroup.homEquiv (puncturedProjectiveLine k)).symm
    (puncturedProjectiveLineCoordinateUnit k) ≫ eqToHom gmInt_eq_overInt_left.symm

/-- The coordinate morphism and the projective structure morphism agree over integral scalars. -/
theorem puncturedProjectiveLine_lift_w (k : Type u) [Field k] :
    puncturedProjectiveLineToIntegral k ≫ eqToHom gmInt_eq_overInt_left ≫ overInt.hom =
      (chartX k ⊓ chartY k).ι ≫ toSpec k ≫
        specULiftZIsTerminal.from (Spec (CommRingCat.of k)) := sorry

/-- The multiplicative group is isomorphic to the projective line minus zero and infinity. -/
def multiplicativeGroup_eq_puncturedProjectiveLine (k : Type u) [Field k] :
    Gm k ≅ puncturedProjectiveLine k where
  hom := IsOpenImmersion.lift (chartX k ⊓ chartY k).ι
    (multiplicativeGroup_to_projectiveLine k) (multiplicativeGroup_to_projectiveLine_mem k)
  inv := pullback.lift
    (puncturedProjectiveLineToIntegral k ≫ eqToHom gmInt_eq_overInt_left)
    ((chartX k ⊓ chartY k).ι ≫ toSpec k) (puncturedProjectiveLine_lift_w k)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheaf pullback of `μₙ` along a scheme morphism. -/
abbrev pulledRootsSheaf {T S : Scheme.{u}} (f : T ⟶ S) (n : ℕ)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
      S.smallEtaleTopology T.smallEtaleTopology).obj (rootsSheaf S n)

/-- Sheaf pullback along small étale base change is additive. -/
instance smallEtaleSheafPullback_additive {T S : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).Additive := sorry

/-- Sheaf pullback along small étale base change preserves finite limits. -/
instance smallEtaleSheafPullback_preservesFiniteLimits {T S : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology) := sorry

/-- Sheaf pullback along small étale base change preserves finite colimits. -/
instance smallEtaleSheafPullback_preservesFiniteColimits {T S : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    PreservesFiniteColimits
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology) := sorry

/-- Restriction of structure sheaves along `f`, as a map into the small étale
pushforward of `𝒪_T`. -/
def smallEtaleStructureSheafPushforwardHom {T S : Scheme.{u}} (f : T ⟶ S) :
    smallCommStructureSheaf .etale S ⟶
      ((smallEtalePullback f).sheafPushforwardContinuous CommRingCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).obj
        (smallCommStructureSheaf .etale T) :=
  ObjectProperty.homMk
    { app := fun U ↦
        (CommRingCat.universeLift.{u, u + 1}).map
          (Scheme.Γ.map (Limits.pullback.fst U.unop.hom f).op)
      naturality := fun {_ _} _ ↦ sorry }

/-- Pushforward of the additive units sheaf agrees with units of the
pushed-forward structure sheaf. -/
theorem unitsAddSheaf_sheafPushforwardContinuous {T S : Scheme.{u}} (f : T ⟶ S) :
    CategoryTheory.Sheaf.unitsAddSheaf
        (((smallEtalePullback f).sheafPushforwardContinuous CommRingCat.{u + 1}
          S.smallEtaleTopology T.smallEtaleTopology).obj
          (smallCommStructureSheaf .etale T)) =
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).obj
        (CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale T)) := sorry

/-- Induced map on additive units sheaves on the small étale site of `S`. -/
def unitsAddSheafPushforwardHom {T S : Scheme.{u}} (f : T ⟶ S) :
    CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale S) ⟶
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).obj
        (CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale T)) :=
  CategoryTheory.Sheaf.unitsAddMap (smallEtaleStructureSheafPushforwardHom f) ≫
    eqToHom (unitsAddSheaf_sheafPushforwardContinuous f)

/-- Adjoint transpose of `unitsAddSheafPushforwardHom`. -/
def unitsAddSheafPullbackHom {T S : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
      S.smallEtaleTopology T.smallEtaleTopology).obj
      (CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale S)) ⟶
    CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale T) :=
  ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      S.smallEtaleTopology T.smallEtaleTopology).homEquiv _ _ |>.symm
    (unitsAddSheafPushforwardHom f)

/-- Comparison of `μₙ` after small étale pullback, from the pulled-back Kummer kernel. -/
def rootsSheafPullbackHom {T S : Scheme.{u}} (f : T ⟶ S) (n : ℕ)
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    pulledRootsSheaf f n ⟶ rootsSheaf T n :=
  kernel.lift (CategoryTheory.Sheaf.unitsNsmul (smallCommStructureSheaf .etale T) n)
    (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
          S.smallEtaleTopology T.smallEtaleTopology).map
        (kernel.ι (CategoryTheory.Sheaf.unitsNsmul
          (smallCommStructureSheaf .etale S) n)) ≫
      unitsAddSheafPullbackHom f)
    sorry

/-- Base change of a terminal small étale object is terminal. -/
def smallEtalePullbackTerminal {T S : Scheme.{u}} (f : T ⟶ S) :
    IsTerminal ((smallEtalePullback f).obj (⊤_ S.Etale)) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk
      (pullback.lift
        (U.hom ≫ f ≫
          (terminal.from (MorphismProperty.Over.mk (P := @Etale) ⊤ (𝟙 S) inferInstance) :
            MorphismProperty.Over.mk (P := @Etale) ⊤ (𝟙 S) inferInstance ⟶ ⊤_ S.Etale).left)
        U.hom sorry) sorry)
    sorry

/-- Inverse image preserves constant additive-group sheaves. -/
def constantSheafPullbackIso {T S : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
    (A : AddCommGrpCat.{u + 1}) :
    ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
      S.smallEtaleTopology T.smallEtaleTopology).obj
      ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) ≅
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
  ((constantSheafAdj S.smallEtaleTopology AddCommGrpCat.{u + 1}
      (terminalIsTerminal : IsTerminal (⊤_ S.Etale))).comp
    ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      S.smallEtaleTopology T.smallEtaleTopology)).leftAdjointUniq
        (constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
          (smallEtalePullbackTerminal f)) |>.app A

/-- Inverse image preserves the constant integer sheaf. -/
def constantIntegerPullbackIso {T S : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
      S.smallEtaleTopology T.smallEtaleTopology).obj
      ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≅
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  constantSheafPullbackIso f (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Inverse image preserves constant cyclic coefficient sheaves. -/
def constantZModPullbackIso {T S : Scheme.{u}} (f : T ⟶ S) (n : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
      S.smallEtaleTopology T.smallEtaleTopology).obj (constantZModSheaf S n) ≅
      constantZModSheaf T n :=
  constantSheafPullbackIso f (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

/-- Pullback of a `μₙ`-cohomology class along a scheme morphism. -/
def rootsH1Pullback {T S : Scheme.{u}} (f : T ⟶ S) (n : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    (rootsSheaf S n).H 1 →+ (rootsSheaf T n).H 1 :=
  AddMonoidHom.mk'
    (fun x ↦
      CategoryTheory.Sheaf.H.map (rootsSheafPullbackHom f n) 1
        ((Ext.mk₀ (constantIntegerPullbackIso f).inv).comp
          (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
                S.smallEtaleTopology T.smallEtaleTopology).mapExtAddHom
            ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
            (rootsSheaf S n) 1 x)
          (zero_add (1 : ℕ))))
    sorry

/-- Pullback of a constant cyclic-coefficient cohomology class along a scheme morphism. -/
def constantH1Pullback {T S : Scheme.{u}} (f : T ⟶ S) (n : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint] :
    (constantZModSheaf S n).H 1 →+ (constantZModSheaf T n).H 1 :=
  AddMonoidHom.mk'
    (fun x ↦
      CategoryTheory.Sheaf.H.map (constantZModPullbackIso f n).hom 1
        ((Ext.mk₀ (constantIntegerPullbackIso f).inv).comp
          (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u + 1}
                S.smallEtaleTopology T.smallEtaleTopology).mapExtAddHom
            ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
            (constantZModSheaf S n) 1 x)
          (zero_add (1 : ℕ))))
    sorry

variable (n : ℕ)

/-- Étale-local lifts of a base morphism through the integral power cover. -/
def kummerLift (S : Scheme.{u}) (f : S ⟶ GmInt) (n : ℕ)
    (U : S.Etaleᵒᵖ) : Type (u + 1) :=
  ULift.{u + 1, u} { lift : U.unop.left ⟶ overInt.left //
    lift ≫ eqToHom gmInt_eq_overInt_left.symm ≫ powerMap n = U.unop.hom ≫ f }

/-- Restriction of lifts through the power cover is given by composition. -/
def kummerLiftRes (S : Scheme.{u}) (f : S ⟶ GmInt) (n : ℕ)
    {U V : S.Etaleᵒᵖ} (g : U ⟶ V) :
    kummerLift S f n U → kummerLift S f n V :=
  fun lift ↦ ⟨⟨g.unop.left ≫ lift.down.val, sorry⟩⟩

/-- The presheaf of étale-local lifts through the power cover. -/
def kummerLiftPresheaf (S : Scheme.{u}) (f : S ⟶ GmInt) (n : ℕ) :
    S.Etaleᵒᵖ ⥤ Type (u + 1) where
  obj := kummerLift S f n
  map g := TypeCat.ofHom (kummerLiftRes S f n g)
  map_id := sorry
  map_comp := sorry

/-- Étale-local lifts through the power cover satisfy the sheaf condition. -/
theorem kummerLiftPresheaf_isSheaf (S : Scheme.{u}) (f : S ⟶ GmInt) (n : ℕ) :
    Presheaf.IsSheaf S.smallEtaleTopology (kummerLiftPresheaf S f n) := sorry

/-- The small étale sheaf of lifts through the power cover. -/
def kummerLiftSheaf (S : Scheme.{u}) (f : S ⟶ GmInt) (n : ℕ) :
    Sheaf S.smallEtaleTopology (Type (u + 1)) :=
  ⟨kummerLiftPresheaf S f n, kummerLiftPresheaf_isSheaf S f n⟩

/-- A roots-of-unity sheaf section determines a unit in global functions. -/
def rootsSectionToUnit (S : Scheme.{u}) (n : ℕ) {U : S.Etaleᵒᵖ}
    (root : (CategoryTheory.Sheaf.toSheafOfGroups (rootsSheaf S n)).1.obj U) :
    Γ(U.unop.left, ⊤)ˣ :=
  let unit := CategoryTheory.Sheaf.unitsAddSheafUnit (smallCommStructureSheaf .etale S)
    ((kernel.ι (CategoryTheory.Sheaf.unitsNsmul
        (smallCommStructureSheaf .etale S) n)).hom.app U
      (CategoryTheory.Sheaf.toSheafOfGroupsValue (rootsSheaf S n) root))
  Units.mk unit.val.down unit.inv.down sorry sorry

/-- Roots-of-unity sections act on lifts by multiplication of coordinates. -/
def kummerSMul (S : Scheme.{u}) (f : S ⟶ GmInt) (n : ℕ) (U : S.Etale)
    (root : (CategoryTheory.Sheaf.toSheafOfGroups (rootsSheaf S n)).1.obj (op U))
    (lift : kummerLift S f n (op U)) : kummerLift S f n (op U) :=
  ⟨⟨(AlgebraicGeometry.MultiplicativeGroup.homEquiv U.left).symm
    (rootsSectionToUnit S n root *
      AlgebraicGeometry.MultiplicativeGroup.homEquiv U.left lift.down.val), sorry⟩⟩

/-- Over a field where `n` is invertible, the power cover defines an étale Kummer torsor. -/
def kummerSheafTorsor (k : Type u) [Field k] (n : ℕ)
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    CategoryTheory.Sheaf.Torsor
      (CategoryTheory.Sheaf.toSheafOfGroups (rootsSheaf (Gm k) n)) where
  carrier := kummerLiftSheaf (Gm k) (gmToInt k) n
  mulAction U :=
    { smul := kummerSMul (Gm k) (gmToInt k) n U
      one_smul := sorry
      mul_smul := sorry }
  act_naturality := sorry
  isPretransitive := sorry
  isCancelSMul := sorry
  locallyNonempty := sorry

variable {k : Type u} [Field k]
variable [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The canonical Kummer class is the class of the field pullback of the integral power cover. -/
def canonicalClass (h_pos : 0 < n) (h_n : IsUnit (n : k)) : h1Roots k n :=
  CategoryTheory.Sheaf.Torsor.Cohomology.classMap.{u + 1, u, u + 1}
    (rootsSheaf (Gm k) n) (Quotient.mk'' (kummerSheafTorsor k n h_pos h_n))

/-- Additivity of the generator map `ZMod n → H¹_étale(𝔾ₘ,k, μₙ)`. -/
theorem rootsH1FromZMod_add (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x y : ZMod n) :
    ((x + y).val : ℤ) • canonicalClass n h_pos h_n =
      ((x.val : ℤ) • canonicalClass n h_pos h_n) +
        ((y.val : ℤ) • canonicalClass n h_pos h_n) := sorry

/-- The comparison `ZMod n → H¹_étale(𝔾ₘ,k, μₙ)` sending `1` to the canonical Kummer class. -/
def rootsH1FromZMod (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    ZMod n →+ h1Roots k n :=
  AddMonoidHom.mk' (fun z ↦ (z.val : ℤ) • canonicalClass n h_pos h_n)
    (rootsH1FromZMod_add n h_pos h_n)

/-- Field-map pullback carries the canonical Kummer class to the canonical class over the larger field. -/
theorem canonicalClass_pullback {k' : Type u} [Field k'] [Algebra k k']
    [HasSheafify (Gm k').smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (Gm k').smallEtaleTopology AddCommGrpCat.{u + 1})]
    [((smallEtalePullback (gmMap k k')).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Gm k).smallEtaleTopology (Gm k').smallEtaleTopology).IsRightAdjoint]
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (h_n' : IsUnit (n : k')) :
    rootsH1Pullback (gmMap k k') n (canonicalClass (k := k) n h_pos h_n) =
      canonicalClass (k := k') n h_pos h_n' := sorry

variable [IsAlgClosed k]

/-- Every class in `H¹_étale(𝔾ₘ,k, μₙ)` is uniquely a `ZMod n`-multiple of the canonical Kummer class. -/
theorem existsUnique_zmod_smul_canonicalClass (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : h1Roots k n) :
    ∃! z : ZMod n, rootsH1FromZMod n h_pos h_n z = x := sorry

/-- The unique coefficient of a cohomology class relative to the canonical Kummer generator. -/
def rootsH1ComparisonFunction (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    h1Roots k n → ZMod n :=
  fun x ↦ Classical.choose (existsUnique_zmod_smul_canonicalClass n h_pos h_n x)

/-- The comparison function preserves addition. -/
theorem rootsH1ComparisonFunction_add (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x y : h1Roots k n) :
    rootsH1ComparisonFunction n h_pos h_n (x + y) =
      rootsH1ComparisonFunction n h_pos h_n x +
        rootsH1ComparisonFunction n h_pos h_n y := sorry

/-- Left inverse law for the Kummer comparison on `𝔾ₘ`. -/
theorem rootsH1ComparisonFunction_leftInverse (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : h1Roots k n) :
    rootsH1FromZMod n h_pos h_n
        (rootsH1ComparisonFunction n h_pos h_n x) = x := sorry

/-- Right inverse law for the Kummer comparison on `𝔾ₘ`. -/
theorem rootsH1ComparisonFunction_rightInverse (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : ZMod n) :
    rootsH1ComparisonFunction n h_pos h_n
        (rootsH1FromZMod n h_pos h_n x) = x := sorry

/-- Canonical isomorphism `H¹_étale(𝔾ₘ,k, μₙ) ≃+ ZMod n`. -/
def etaleCohomology_Gm_rootsOfUnity_h1 (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    h1Roots k n ≃+ ZMod n where
  toFun := rootsH1ComparisonFunction n h_pos h_n
  invFun := rootsH1FromZMod n h_pos h_n
  left_inv := rootsH1ComparisonFunction_leftInverse n h_pos h_n
  right_inv := rootsH1ComparisonFunction_rightInverse n h_pos h_n
  map_add' := rootsH1ComparisonFunction_add n h_pos h_n

/-- The canonical isomorphism sends the canonical Kummer class to `1 : ZMod n`. -/
theorem etaleCohomology_Gm_rootsOfUnity_h1_canonicalClass
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    etaleCohomology_Gm_rootsOfUnity_h1 n h_pos h_n
        (canonicalClass n h_pos h_n) = (1 : ZMod n) := sorry

variable {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
variable [HasSheafify (Gm k').smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf (Gm k').smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [((smallEtalePullback (gmMap k k')).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Gm k).smallEtaleTopology (Gm k').smallEtaleTopology).IsRightAdjoint]

section CoefficientCoordinates

omit [HasSheafify (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- A chosen primitive `n`th root of unity in an algebraically closed field. -/
def chosenPrimitiveRoot (h_pos : 0 < n) (h_n : IsUnit (n : k)) : kˣ :=
  let roots := @IsSepClosed.hasEnoughRootsOfUnity k inferInstance n
    ⟨h_n.ne_zero⟩ inferInstance
  let ζ := (@HasEnoughRootsOfUnity.exists_primitiveRoot k inferInstance n roots).choose
  Units.mk0 ζ sorry

/-- The chosen unit is a primitive `n`th root of unity. -/
theorem chosenPrimitiveRoot_spec (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    IsPrimitiveRoot (chosenPrimitiveRoot (k := k) n h_pos h_n) n := sorry

/-- An additive identification `μₙ(k) ≃+ ZMod n`. -/
def rootsOfUnityAddEquivZMod (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    Additive (rootsOfUnity n k) ≃+ ZMod n :=
  let powers_eq := @IsPrimitiveRoot.zpowers_eq k inferInstance inferInstance n
    ⟨Nat.ne_zero_of_lt h_pos⟩ (chosenPrimitiveRoot (k := k) n h_pos h_n)
      (chosenPrimitiveRoot_spec (k := k) n h_pos h_n)
  (MulEquiv.subgroupCongr powers_eq.symm).toAdditive.trans
    (chosenPrimitiveRoot_spec (k := k) n h_pos h_n).zmodEquivZPowers.symm

/-- The inverse coefficient identification sends a natural residue to the corresponding
power of the chosen primitive root. -/
@[simp]
theorem rootsOfUnityAddEquivZMod_symm_apply_natCast
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) (m : ℕ) :
    ((rootsOfUnityAddEquivZMod (k := k) n h_pos h_n).symm (m : ZMod n)).toMul.val =
      chosenPrimitiveRoot (k := k) n h_pos h_n ^ m := sorry

end CoefficientCoordinates

/-- Constant sheaf of `μₙ(k)` on the small étale site of `𝔾ₘ,k`. -/
abbrev constantRootsSheaf :
    Sheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (Additive (rootsOfUnity n k))))

/-- Twist isomorphism of coefficient groups `μₙ(k) ≃ ZMod n`, lifted to constant sheaves. -/
def constantRootsIsoConstantZMod (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    constantRootsSheaf (k := k) (n := n) ≅ constantZModSheaf (Gm k) n :=
  (constantSheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
    (AddEquiv.ulift.trans
        ((rootsOfUnityAddEquivZMod (k := k) n h_pos h_n).trans AddEquiv.ulift.symm)).toAddCommGrpIso

/-- The structure morphism `𝔾ₘ,k ⟶ Spec k`. -/
def gmToSpec (k : Type u) [Field k] :
    Gm k ⟶ Spec (CommRingCat.of k) :=
  pullback.snd overInt.hom (specULiftZIsTerminal.from (Spec (CommRingCat.of k)))

/-- Global functions of an étale object over `𝔾ₘ,k` receive the structure map from `k`. -/
def etaleStructureRingHom (U : (Gm k).Etale) : k →+* Γ(U.left, ⊤) :=
  CommRingCat.Hom.hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.hom ≫ gmToSpec k).appTop)

/-- The terminal object of the small étale site of `𝔾ₘ,k`. -/
abbrev gmEtaleTerminal (k : Type u) [Field k] : (Gm k).Etale :=
  ⊤_ (Gm k).Etale

/-- Send a root of unity in `k` to the corresponding additive-units section over the terminal. -/
def constantRootToUnitsTerminal (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    AddCommGrpCat.of (ULift.{u + 1} (Additive (rootsOfUnity n k))) ⟶
      (CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale (Gm k))).1.obj
        (op (gmEtaleTerminal k)) :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (fun ζ : ULift.{u + 1} (Additive (rootsOfUnity n k)) ↦
        CategoryTheory.Sheaf.unitsAddSheafSection (smallCommStructureSheaf .etale (Gm k))
          (Units.mk
            (ULift.up
              ((etaleStructureRingHom (k := k) (gmEtaleTerminal k))
                ζ.down.toMul.val.val))
            (ULift.up
              ((etaleStructureRingHom (k := k) (gmEtaleTerminal k))
                ζ.down.toMul.val.inv))
            sorry sorry))
      sorry)

/-- The sheaf map from the constant sheaf of `μₙ(k)` to additive units. -/
def constantRootsToUnits (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    constantRootsSheaf (k := k) (n := n) ⟶
      CategoryTheory.Sheaf.unitsAddSheaf (smallCommStructureSheaf .etale (Gm k)) :=
  ((constantSheafAdj (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}
      (terminalIsTerminal : IsTerminal (⊤_ (Gm k).Etale))).homEquiv _ _).symm
    (constantRootToUnitsTerminal (k := k) n h_pos h_n)

/-- The sheaf map from the constant sheaf of `μₙ(k)` to the Kummer kernel. -/
def constantRootsToRoots (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    constantRootsSheaf (k := k) (n := n) ⟶ rootsSheaf (Gm k) n :=
  kernel.lift (CategoryTheory.Sheaf.unitsNsmul (smallCommStructureSheaf .etale (Gm k)) n)
    (constantRootsToUnits n h_pos h_n) sorry

/-- The Kummer sheaf map to the constant sheaf of `μₙ(k)` is the inverse of
`constantRootsToRoots`. -/
instance constantRootsToRoots_isIso (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    IsIso (constantRootsToRoots (k := k) n h_pos h_n) := sorry

/-- The inverse constant-roots comparison identifies Kummer sections with constant roots. -/
def rootsToConstantRoots (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    rootsSheaf (Gm k) n ⟶ constantRootsSheaf (k := k) (n := n) :=
  (asIso (constantRootsToRoots (k := k) n h_pos h_n)).inv

/-- The Kummer coefficient sheaf is canonically isomorphic to constant roots of unity. -/
def rootsSheafIsoConstantRoots (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    rootsSheaf (Gm k) n ≅ constantRootsSheaf (k := k) (n := n) :=
  (asIso (constantRootsToRoots (k := k) n h_pos h_n)).symm

/-- Twist isomorphism `μₙ ≅` the constant sheaf `ZMod n` on `𝔾ₘ,k`. -/
def rootsSheafIsoConstantZMod (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    rootsSheaf (Gm k) n ≅ constantZModSheaf (Gm k) n :=
  rootsSheafIsoConstantRoots n h_pos h_n ≪≫
    constantRootsIsoConstantZMod n h_pos h_n

/-- A character of roots of unity induces a morphism of constant coefficient sheaves. -/
def constantRootsToZMod (character : Additive (rootsOfUnity n k) →+ ZMod n) :
    constantRootsSheaf (k := k) (n := n) ⟶ constantZModSheaf (Gm k) n :=
  (constantSheaf (Gm k).smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (AddCommGrpCat.ofHom
      ((AddEquiv.ulift.symm.toAddMonoidHom.comp character).comp
        AddEquiv.ulift.toAddMonoidHom))

/-- The comparison function from constant `ZMod n` cohomology to `Hom(μₙ(k), ZMod n)`,
obtained by twisting the `μₙ` isomorphism. -/
def constantH1ComparisonFunction (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    h1Constant k n → (Additive (rootsOfUnity n k) →+ ZMod n) :=
  fun x ↦
    (AddMonoidHom.mulLeft
        (etaleCohomology_Gm_rootsOfUnity_h1 n h_pos h_n
          (CategoryTheory.Sheaf.H.map (rootsSheafIsoConstantZMod n h_pos h_n).inv 1 x))).comp
      (rootsOfUnityAddEquivZMod n h_pos h_n).toAddMonoidHom

/-- Additivity of the twisted comparison. -/
theorem constantH1ComparisonFunction_add (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x y : h1Constant k n) :
    constantH1ComparisonFunction n h_pos h_n (x + y) =
      constantH1ComparisonFunction n h_pos h_n x +
        constantH1ComparisonFunction n h_pos h_n y := sorry

/-- A character sends the canonical Kummer class to its constant-coefficient cohomology class. -/
def constantH1FromHom (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    (Additive (rootsOfUnity n k) →+ ZMod n) → h1Constant k n :=
  fun character ↦ CategoryTheory.Sheaf.H.map
    ((rootsSheafIsoConstantRoots n h_pos h_n).hom ≫ constantRootsToZMod n character) 1
    (canonicalClass n h_pos h_n)

/-- Left inverse law for the twisted comparison. -/
theorem constantH1ComparisonFunction_leftInverse (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : h1Constant k n) :
    constantH1FromHom n h_pos h_n
        (constantH1ComparisonFunction n h_pos h_n x) = x := sorry

/-- Right inverse law for the twisted comparison. -/
theorem constantH1ComparisonFunction_rightInverse (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : Additive (rootsOfUnity n k) →+ ZMod n) :
    constantH1ComparisonFunction n h_pos h_n
        (constantH1FromHom n h_pos h_n x) = x := sorry

/-- Canonical isomorphism `H¹_étale(𝔾ₘ,k, ZMod n) ≃+ Hom(μₙ(k), ZMod n)`. -/
def etaleCohomology_Gm_constantZMod_h1 (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    h1Constant k n ≃+ (Additive (rootsOfUnity n k) →+ ZMod n) where
  toFun := constantH1ComparisonFunction n h_pos h_n
  invFun := constantH1FromHom n h_pos h_n
  left_inv := constantH1ComparisonFunction_leftInverse n h_pos h_n
  right_inv := constantH1ComparisonFunction_rightInverse n h_pos h_n
  map_add' := constantH1ComparisonFunction_add n h_pos h_n

/-- The constant-coefficient cohomology comparison commutes with extensions of algebraically closed fields. -/
theorem etaleCohomology_Gm_constantZMod_h1_naturality
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) (h_n' : IsUnit (n : k'))
    (x : h1Constant k n) :
    (etaleCohomology_Gm_constantZMod_h1 (k := k') n h_pos h_n'
      (constantH1Pullback (gmMap k k') n x)).comp
        (restrictRootsOfUnity (algebraMap k k') n).toAdditive =
      etaleCohomology_Gm_constantZMod_h1 (k := k) n h_pos h_n x := sorry

end AlgebraicGeometry.EtaleCohomology.MultiplicativeGroup

end
