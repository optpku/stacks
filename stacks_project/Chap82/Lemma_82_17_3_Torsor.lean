module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Universal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Functoriality
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Sober
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_20_8_Over
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_4_8
public import stacks_project.Chap67.Lemma_67_23_2
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra
public import stacks_project.Chap76.Lemma_76_25_1_Pullback
public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap71.Lemma_71_16_4_Conormal
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# The G_m-torsor of an invertible module on an algebraic space

The relative spectrum of the ℤ-graded tensor-power algebra of an invertible
𝒪_X-module, together with its structure morphism, tautological trivialization,
base change, and henselian comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConcreteCategory CategoryTheory.Functor
open CategoryTheory.MonoidalCategory.InvertiblePower
open Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IdealSubobject
open SheafOfModules.RingedSite SheafOfModules.RingedSite.ModuleSheafification
open RingedSite.ToposHom IsLocalRing
open scoped DirectSum TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Homogeneous sections of the integral tensor power of an invertible module. -/
abbrev tensorPowerSection (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) (n : ℤ) : Type u :=
  (InvertiblePower.obj L n).val.obj U

/-- The image of a structure-sheaf section in the monoidal unit of `X.Modules`. -/
noncomputable def tensorUnitSection (U : (smallEtaleSite X)ᵒᵖ)
    (r : (commStructureSheaf X).obj.obj U) :
    (𝟙_ X.Modules).val.obj U :=
  (((ofCommModules X).map
      (unitIsoTensorUnit (J := smallEtaleTopology X)
        (𝒪 := commStructureSheaf X)).hom).val.app U).hom r

/-- Pointwise tensor of homogeneous sections, sheafified as a module over
`commStructureSheaf`. -/
noncomputable def pointwiseToSheafified (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) (m n : ℤ)
    (t : tensorPowerSection L U m ⊗[↑((commStructureSheaf X).obj.obj U)]
      tensorPowerSection L U n) :=
  (moduleSheafificationUnitToVal (commStructureSheaf X)
    (PresheafOfModules.Monoidal.tensorObj
      (toComm (InvertiblePower.obj L m)).val
      (toComm (InvertiblePower.obj L n)).val)).app U t

/-- Insertion of a homogeneous section into the right-unitor tensor `M ⊗ 𝟙`. -/
noncomputable def tensorRightUnitSection (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) (m : ℤ) (x : tensorPowerSection L U m) :
    ((InvertiblePower.obj L m) ⊗ 𝟙_ X.Modules).val.obj U :=
  ((ρ_ (InvertiblePower.obj L m)).inv.val.app U).hom x

/-- The sheaf-tensor section associated to a pair of homogeneous sections. -/
noncomputable def tensorPairSection (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) (m n : ℤ)
    (x : tensorPowerSection L U m) (y : tensorPowerSection L U n) :
    ((InvertiblePower.obj L m) ⊗ InvertiblePower.obj L n).val.obj U :=
  (commTensorComparison (InvertiblePower.obj L m) (InvertiblePower.obj L n)).val.app U
    ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf X)
        (PresheafOfModules.Monoidal.tensorObj
          ((toCommModules X).obj (InvertiblePower.obj L m)).val
          ((toCommModules X).obj (InvertiblePower.obj L n)).val)).app U
      (x ⊗ₜ y))

/-- Multiplication of homogeneous sections induced by `InvertiblePower.addIso`. -/
noncomputable def mulSection (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) (m n : ℤ)
    (x : tensorPowerSection L U m) (y : tensorPowerSection L U n) :
    tensorPowerSection L U (m + n) :=
  ((InvertiblePower.addIso L m n).hom.val.app U).hom (tensorPairSection L U m n x y)

/-- The canonical unit section of the zeroth integral tensor power. -/
noncomputable def oneSection (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) : tensorPowerSection L U 0 :=
  ((InvertiblePower.zeroIso L).inv.val.app U).hom (tensorUnitSection U 1)

variable (L : X.Modules) [isInvertibleObject L]
variable (U : (smallEtaleSite X)ᵒᵖ)

/-- Homogeneous multiplication on integral tensor-power sections. -/
instance instGMul : GradedMonoid.GMul (tensorPowerSection L U) where
  mul := fun {m n} => mulSection L U m n

/-- The degree-zero unit section. -/
instance instGOne : GradedMonoid.GOne (tensorPowerSection L U) where
  one := oneSection L U

/-- Graded monoid laws for integral tensor-power sections. -/
instance instGMonoid : GradedMonoid.GMonoid (tensorPowerSection L U) where
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

/-- Homogeneous sections of integral tensor powers commute. -/
instance instGCommMonoid : GradedMonoid.GCommMonoid (tensorPowerSection L U) where
  mul_comm := sorry

/-- Bilinear vanishing laws for homogeneous multiplication. -/
instance instGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (tensorPowerSection L U) where
  mul_zero := sorry
  zero_mul := sorry
  mul_add := sorry
  add_mul := sorry

/-- Graded semiring structure on integral tensor-power sections. -/
instance instGSemiring : DirectSum.GSemiring (tensorPowerSection L U) where
  natCast n := n • GradedMonoid.GOne.one
  natCast_zero := sorry
  natCast_succ := sorry

/-- Graded commutative semiring structure on integral tensor-power sections. -/
instance instGCommSemiring : DirectSum.GCommSemiring (tensorPowerSection L U) where

/-- Graded ring structure on integral tensor-power sections. -/
instance instGRing : DirectSum.GRing (tensorPowerSection L U) where
  intCast z := z • GradedMonoid.GOne.one
  intCast_ofNat := sorry
  intCast_negSucc_ofNat := sorry

/-- Graded commutative ring structure on integral tensor-power sections. -/
instance instGCommRing : DirectSum.GCommRing (tensorPowerSection L U) where

/-- Restriction of a homogeneous tensor-power section along an étale morphism. -/
noncomputable def tensorPowerRestrict {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (n : ℤ) :
    tensorPowerSection L U n →+ tensorPowerSection L V n :=
  ((InvertiblePower.obj L n).val.map i).hom.toAddMonoidHom

/-- Additive restriction of the integer-graded tensor-power DirectSum. -/
noncomputable def invertibleLaurentRestrict {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    DirectSum ℤ (tensorPowerSection L U) →+ DirectSum ℤ (tensorPowerSection L V) :=
  DirectSum.map fun n => tensorPowerRestrict (L := L) (U := U) i n

/-- Ring restriction of the integer-graded tensor-power DirectSum. -/
noncomputable def invertibleLaurentRestrictRingHom {U V : (smallEtaleSite X)ᵒᵖ}
    (i : U ⟶ V) :
    DirectSum ℤ (tensorPowerSection L U) →+* DirectSum ℤ (tensorPowerSection L V) :=
  { invertibleLaurentRestrict (L := L) (U := U) i with
    map_one' := sorry
    map_mul' := sorry }

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Commutative-ring-valued weak sheafification exists on the small étale site. -/
instance smallEtaleTopology_hasWeakSheafify_commRingCat :
    HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u} :=
  sorry

/-- Commutative-ring-valued sheafification exists on the small étale site. -/
instance smallEtaleTopology_hasSheafify_commRingCat :
    HasSheafify (smallEtaleTopology X) CommRingCat.{u} :=
  sorry

/-- The presheaf of integer-graded tensor-power algebras of an invertible module. -/
noncomputable def invertibleLaurentPresheaf (L : X.Modules) [isInvertibleObject L] :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (DirectSum ℤ (tensorPowerSection L U))
  map i := CommRingCat.ofHom (invertibleLaurentRestrictRingHom (L := L) i)
  map_id := sorry
  map_comp := sorry

/-- The sheafification of the integer-graded tensor-power algebra of an invertible module. -/
noncomputable def invertibleLaurentSheaf (L : X.Modules) [isInvertibleObject L] :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  (presheafToSheaf (smallEtaleTopology X) CommRingCat.{u}).obj
    (invertibleLaurentPresheaf L)

/-- The unsafified structure map from `𝒪_X` into the tensor-power DirectSum. -/
noncomputable def invertibleLaurentUnit (L : X.Modules) [isInvertibleObject L] :
    (commRingStructureSheaf X).obj ⟶ invertibleLaurentPresheaf L where
  app U :=
    CommRingCat.ofHom
      { toFun := fun r =>
          DirectSum.of (tensorPowerSection L U) 0
            (((InvertiblePower.zeroIso L).inv.val.app U).hom
              (tensorUnitSection U r))
        map_one' := sorry
        map_mul' := sorry
        map_zero' := sorry
        map_add' := sorry }
  naturality := sorry

/-- The canonical structure map from `𝒪_X` to the sheafified tensor-power algebra. -/
noncomputable def invertibleLaurentStructureMap (L : X.Modules) [isInvertibleObject L] :
    commRingStructureSheaf X ⟶ invertibleLaurentSheaf L :=
  CategoryTheory.Sheaf.homEquiv.symm
    (invertibleLaurentUnit L ≫
      toSheafify (smallEtaleTopology X) (invertibleLaurentPresheaf L))

/-- The tensor-power algebra of an invertible module, as an algebra under `𝒪_X`. -/
noncomputable def invertibleLaurentUnder (L : X.Modules) [isInvertibleObject L] :
    Under (commRingStructureSheaf X) :=
  Under.mk (invertibleLaurentStructureMap L)

/-- The underlying module of the tensor-power algebra is quasi-coherent. -/
theorem invertibleLaurent_isQuasicoherent (L : X.Modules) [isInvertibleObject L] :
    ((restrictionAlong (invertibleLaurentUnder L).hom).obj
      (unitModule (smallEtaleTopology X)
        (invertibleLaurentUnder L).right)).IsQuasicoherent :=
  sorry

/-- The quasi-coherent `𝒪_X`-algebra `⨁_{n ∈ ℤ} L^{⊗ n}`. -/
noncomputable def invertibleLaurentAlgebra (L : X.Modules) [isInvertibleObject L] :
    X.QcAlgebraUnder where
  obj := invertibleLaurentUnder L
  property := invertibleLaurent_isQuasicoherent L

/-- The underlying `𝒪_X`-module of the tensor-power algebra. -/
noncomputable def invertibleLaurentModule (L : X.Modules) [isInvertibleObject L] :
    X.Modules :=
  ofComm
    ((restrictionAlong (invertibleLaurentUnder L).hom).obj
      (unitModule (smallEtaleTopology X) (invertibleLaurentUnder L).right))

/-- The canonical `G_m`-torsor of an invertible `𝒪_X`-module. -/
noncomputable def gmTorsor (L : X.Modules) [isInvertibleObject L] : AlgebraicSpace S :=
  relativeSpec (invertibleLaurentAlgebra L)

/-- The structure morphism `q : T ⟶ X` of the `G_m`-torsor of `L`. -/
noncomputable def gmTorsorπ (L : X.Modules) [isInvertibleObject L] : gmTorsor L ⟶ X :=
  relativeSpecπ (invertibleLaurentAlgebra L)

/-- Component of degree-`n` insertion at an étale object, as a morphism of
`𝒪_X`-modules. -/
noncomputable def degreeIncludeApp (L : X.Modules) [isInvertibleObject L] (n : ℤ)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (InvertiblePower.obj L n).val.obj U ⟶ (invertibleLaurentModule L).val.obj U :=
  @ModuleCat.ofHom ((structureSheaf X).obj.obj U) _
    ((InvertiblePower.obj L n).val.obj U)
    ((invertibleLaurentModule L).val.obj U)
    ((InvertiblePower.obj L n).val.obj U).isAddCommGroup
    ((InvertiblePower.obj L n).val.obj U).isModule
    ((invertibleLaurentModule L).val.obj U).isAddCommGroup
    ((invertibleLaurentModule L).val.obj U).isModule
    { toFun := fun x =>
        ((toSheafify (smallEtaleTopology X) (invertibleLaurentPresheaf L)).app U).hom
          (DirectSum.of (tensorPowerSection L U) n x)
      map_add' := sorry
      map_smul' := sorry }

/-- Degree-`n` insertion of an invertible module into the tensor-power algebra. -/
noncomputable def degreeInclude (L : X.Modules) [isInvertibleObject L] (n : ℤ) :
    InvertiblePower.obj L n ⟶ invertibleLaurentModule L where
  val :=
    { app := fun U => degreeIncludeApp L n U
      naturality := sorry }

/-- The `G_m`-torsor is the relative spectrum of the tensor-power algebra. -/
theorem gmTorsor_def (L : X.Modules) [isInvertibleObject L] :
    gmTorsor L = relativeSpec (invertibleLaurentAlgebra L) :=
  rfl

/-- The structure morphism of the `G_m`-torsor is the relative-spectrum projection. -/
theorem gmTorsorπ_def (L : X.Modules) [isInvertibleObject L] :
    gmTorsorπ L = relativeSpecπ (invertibleLaurentAlgebra L) :=
  rfl

/-- Degree-one insertion of `L` into the tensor-power algebra. -/
noncomputable def degreeIncludeOne (L : X.Modules) [isInvertibleObject L] :
    L ⟶ invertibleLaurentModule L :=
  (InvertiblePower.oneIso L).inv ≫ degreeInclude L 1

/-- Degree-zero homogeneous sections map to structure-sheaf sections. -/
noncomputable def degreeZeroToStructure (L : X.Modules) [isInvertibleObject L]
    (U : (smallEtaleSite X)ᵒᵖ) (x : tensorPowerSection L U 0) :
    (commRingStructureSheaf X).obj.obj U :=
  (((ofCommModules X).map
      (unitIsoTensorUnit (J := smallEtaleTopology X)
        (𝒪 := commStructureSheaf X)).inv).val.app U).hom
    (((InvertiblePower.zeroIso L).hom.val.app U).hom x)

/-- The Laurent algebra maps to the structure sheaf of its own relative spectrum by the universal counit. -/
noncomputable def invertibleLaurentToPushforward (L : X.Modules) [isInvertibleObject L] :
    invertibleLaurentSheaf L ⟶
      (commRingPushforward (gmTorsorπ L)).obj (commRingStructureSheaf (gmTorsor L)) :=
  (relativeSpecUniversalAlgebraMap (invertibleLaurentAlgebra L)).right

/-- The commutative pushforward `q_* 𝒪_T`, regarded as an `𝒪_X`-module by restriction
of scalars along `q^♯`. -/
noncomputable def gmTorsorπ_commPushforwardModule (L : X.Modules)
    [isInvertibleObject L] : X.Modules :=
  ofComm
    ((restrictionAlong (commRingStructureSheafMap (gmTorsorπ L))).obj
      (unitModule (smallEtaleTopology X)
        ((commRingPushforward (gmTorsorπ L)).obj
          (commRingStructureSheaf (gmTorsor L)))))

/-- Component of the tautological comparison `⨁_n L^{⊗ n} ⟶ q_* 𝒪_T` at an étale
object, as a morphism of `𝒪_X`-modules. -/
noncomputable def gmTorsorπ_laurentToPushforwardApp (L : X.Modules)
    [isInvertibleObject L] (U : (smallEtaleSite X)ᵒᵖ) :
    (invertibleLaurentModule L).val.obj U ⟶
      (gmTorsorπ_commPushforwardModule L).val.obj U :=
  @ModuleCat.ofHom ((structureSheaf X).obj.obj U) _
    ((invertibleLaurentModule L).val.obj U)
    ((gmTorsorπ_commPushforwardModule L).val.obj U)
    ((invertibleLaurentModule L).val.obj U).isAddCommGroup
    ((invertibleLaurentModule L).val.obj U).isModule
    ((gmTorsorπ_commPushforwardModule L).val.obj U).isAddCommGroup
    ((gmTorsorπ_commPushforwardModule L).val.obj U).isModule
    { toFun := fun x =>
        ((InducedCategory.Hom.hom
            (invertibleLaurentToPushforward L)).app U).hom x
      map_add' := sorry
      map_smul' := sorry }

/-- Underlying module morphism of the tautological comparison `⨁_n L^{⊗ n} ⟶ q_* 𝒪_T`
in the commutative pushforward presentation. -/
noncomputable def gmTorsorπ_laurentToCommPushforward (L : X.Modules)
    [isInvertibleObject L] :
    invertibleLaurentModule L ⟶ gmTorsorπ_commPushforwardModule L where
  val :=
    { app := fun U => gmTorsorπ_laurentToPushforwardApp L U
      naturality := sorry }

/-- Spaces-étale sheaves of commutative rings compose with the forgetful functor
to rings. -/
instance spacesEtaleTopology_hasSheafCompose_forget₂_commRing (Y : AlgebraicSpace S) :
    (spacesEtaleTopology Y).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- Forgetting commutativity preserves the right Kan extensions defining cocontinuous
direct image along `smallEtaleInclusion`. -/
instance forget₂_commRingCat_preservesRightKanExtensions_smallEtaleInclusion
    (Y : AlgebraicSpace S) :
    (forget₂ CommRingCat.{u} RingCat.{u}).PreservesRightKanExtensions
      (smallEtaleInclusion Y).op :=
  sorry

/-- Forgetting commutativity commutes with commutative-ring pushforward. -/
noncomputable def commRingPushforwardForget₂Iso {Y T : AlgebraicSpace S} (f : T ⟶ Y) :
    commRingPushforward f ⋙
        sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology T) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        ringPushforward f :=
  commRingPushforwardForgetIso f

/-- Forgetting all the way to types after commutative-ring pushforward recovers
type-valued direct image. -/
noncomputable def commRingPushforwardForgetTypeIso {Y T : AlgebraicSpace S}
    (f : T ⟶ Y) :
    commRingPushforward f ⋙
        sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
          sheafCompose (smallEtaleTopology Y) (forget RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology T) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        sheafCompose (smallEtaleTopology T) (forget RingCat.{u}) ⋙
          typePushforward f :=
  commRingPushforwardUnderlyingIso f ≪≫ Functor.associator _ _ _

/-- The type-valued sheaf underlying the restricted unit module of a commutative-ring
sheaf maps to the ordinary forgetful type sheaf of that ring sheaf. -/
noncomputable def restrictionUnitCarrierToForget
    {Y : AlgebraicSpace S} {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    (α : commRingStructureSheaf Y ⟶ A) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
        (ofComm ((restrictionAlong α).obj (unitModule (smallEtaleTopology Y) A))) ⟶
      (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj A) :=
  InducedCategory.homMk
    { app := fun U ↦ 𝟙 _
      naturality := fun {_ _} _ ↦ sorry }

/-- The ordinary forgetful type sheaf of a commutative-ring sheaf maps to the
type-valued sheaf underlying the restricted unit module of that ring sheaf. -/
noncomputable def forgetToRestrictionUnitCarrier
    {Y : AlgebraicSpace S} {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    (α : commRingStructureSheaf Y ⟶ A) :
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
        (ofComm ((restrictionAlong α).obj (unitModule (smallEtaleTopology Y) A))) :=
  InducedCategory.homMk
    { app := fun U ↦ 𝟙 _
      naturality := fun {_ _} _ ↦ sorry }

/-- The structure module `𝒪_T` in the commutative étale presentation. -/
noncomputable def gmTorsorStructureModule (L : X.Modules)
    [isInvertibleObject L] : (gmTorsor L).Modules :=
  ofComm
    ((restrictionAlong (𝟙 (commRingStructureSheaf (gmTorsor L)))).obj
      (unitModule (smallEtaleTopology (gmTorsor L))
        (commRingStructureSheaf (gmTorsor L))))

/-- Type-valued comparison of the commutative pushforward unit with the module
pushforward of `gmTorsorStructureModule`. -/
noncomputable def gmTorsorπ_commPushforwardToModulePushforwardUnderlying
    (L : X.Modules) [isInvertibleObject L] :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
        (gmTorsorπ_commPushforwardModule L) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
        ((pushforward (gmTorsorπ L)).obj (gmTorsorStructureModule L)) :=
  restrictionUnitCarrierToForget (commRingStructureSheafMap (gmTorsorπ L)) ≫
    (commRingPushforwardForgetTypeIso (gmTorsorπ L)).hom.app
      (commRingStructureSheaf (gmTorsor L)) ≫
    (typePushforward (gmTorsorπ L)).map
      (forgetToRestrictionUnitCarrier (𝟙 (commRingStructureSheaf (gmTorsor L)))) ≫
    (ModulePushforward.forgetIso (ringedToposHom (gmTorsorπ L))).inv.app
      (gmTorsorStructureModule L)

/-- Module comparison `q_* 𝒪_T` from the commutative presentation to module
pushforward of `gmTorsorStructureModule`. -/
noncomputable def gmTorsorπ_commPushforwardToModulePushforward (L : X.Modules)
    [isInvertibleObject L] :
    gmTorsorπ_commPushforwardModule L ⟶
      (pushforward (gmTorsorπ L)).obj (gmTorsorStructureModule L) :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf X)
    (gmTorsorπ_commPushforwardToModulePushforwardUnderlying L)
    (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- Underlying module morphism of the tautological comparison `⨁_n L^{⊗ n} ⟶ q_* 𝒪_T`. -/
noncomputable def gmTorsorπ_laurentToPushforward (L : X.Modules)
    [isInvertibleObject L] :
    invertibleLaurentModule L ⟶
      (pushforward (gmTorsorπ L)).obj (gmTorsorStructureModule L) :=
  gmTorsorπ_laurentToCommPushforward L ≫
    gmTorsorπ_commPushforwardToModulePushforward L

/-- The forgetful type sheaf of `commRingStructureSheaf Y` maps to the type-valued
sheaf underlying the structure module of `Y`. -/
noncomputable def forgetToStructureUnitCarrier (Y : AlgebraicSpace S) :
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj (commRingStructureSheaf Y)) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
        (SheafOfModules.unit (structureSheaf Y)) :=
  InducedCategory.homMk
    { app := fun U ↦ 𝟙 _
      naturality := fun {_ _} _ ↦ sorry }

/-- Identify the commutative structure module of `T` with the tensor unit of
`T.Modules`. -/
noncomputable def gmTorsorStructureModuleToTensorUnit (L : X.Modules)
    [isInvertibleObject L] :
    gmTorsorStructureModule L ⟶ 𝟙_ (gmTorsor L).Modules :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf (gmTorsor L))
    (restrictionUnitCarrierToForget (𝟙 (commRingStructureSheaf (gmTorsor L))) ≫
      forgetToStructureUnitCarrier (gmTorsor L) ≫
      (Sheaf.InternalModule.ToInternal.underlying
          (structureSheaf (gmTorsor L))).map
        (structureModuleIsoTensorUnit (gmTorsor L)).hom)
    (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- The type-valued sheaf underlying the structure module of `Y` maps to the
forgetful type sheaf of `commRingStructureSheaf Y`. -/
noncomputable def structureUnitCarrierToForget (Y : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
        (SheafOfModules.unit (structureSheaf Y)) ⟶
      (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj (commRingStructureSheaf Y)) :=
  InducedCategory.homMk
    { app := fun U ↦ 𝟙 _
      naturality := fun {_ _} _ ↦ sorry }

/-- `structureUnitCarrierToForget` is inverse to `forgetToStructureUnitCarrier`
on underlying type sheaves. -/
theorem structureUnitCarrierToForget_comp (Y : AlgebraicSpace S) :
    forgetToStructureUnitCarrier Y ≫ structureUnitCarrierToForget Y = 𝟙 _ :=
  sorry

/-- Reverse comparison of the commutative structure module of `T` with the
tensor unit of `T.Modules`. -/
noncomputable def tensorUnitToGmTorsorStructureModule (L : X.Modules)
    [isInvertibleObject L] :
    𝟙_ (gmTorsor L).Modules ⟶ gmTorsorStructureModule L :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf (gmTorsor L))
    ((Sheaf.InternalModule.ToInternal.underlying
          (structureSheaf (gmTorsor L))).map
        (structureModuleIsoTensorUnit (gmTorsor L)).inv ≫
      structureUnitCarrierToForget (gmTorsor L) ≫
      forgetToRestrictionUnitCarrier (𝟙 (commRingStructureSheaf (gmTorsor L))))
    (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- Canonical isomorphism of the commutative structure module of `T` with the
tensor unit `𝒪_T`. -/
noncomputable def gmTorsorStructureModuleIsoTensorUnit (L : X.Modules)
    [isInvertibleObject L] :
    gmTorsorStructureModule L ≅ 𝟙_ (gmTorsor L).Modules where
  hom := gmTorsorStructureModuleToTensorUnit L
  inv := tensorUnitToGmTorsorStructureModule L
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `gmTorsorStructureModuleIsoTensorUnit` is the
structure-module comparison. -/
theorem gmTorsorStructureModuleIsoTensorUnit_hom (L : X.Modules)
    [isInvertibleObject L] :
    (gmTorsorStructureModuleIsoTensorUnit L).hom =
      gmTorsorStructureModuleToTensorUnit L :=
  rfl

/-- The inverse of `gmTorsorStructureModuleIsoTensorUnit` is the reverse
structure-module comparison. -/
theorem gmTorsorStructureModuleIsoTensorUnit_inv (L : X.Modules)
    [isInvertibleObject L] :
    (gmTorsorStructureModuleIsoTensorUnit L).inv =
      tensorUnitToGmTorsorStructureModule L :=
  rfl

/-- The adjunct of degree-one insertion, as a morphism `q^* L ⟶ 𝒪_T`. -/
noncomputable def gmTorsorTrivHom (L : X.Modules) [isInvertibleObject L] :
    (pullback (gmTorsorπ L)).obj L ⟶ gmTorsorStructureModule L :=
  ((pullbackPushforwardAdjunction (gmTorsorπ L)).homEquiv
      L (gmTorsorStructureModule L)).symm
    (degreeIncludeOne L ≫ gmTorsorπ_laurentToPushforward L)

/-- The adjunct of degree-minus-one insertion, as a morphism
`q^* L^{⊗ -1} ⟶ 𝒪_T`. -/
noncomputable def gmTorsorDegreeNegOneHom (L : X.Modules)
    [isInvertibleObject L] :
    (pullback (gmTorsorπ L)).obj (obj L (-1)) ⟶ gmTorsorStructureModule L :=
  ((pullbackPushforwardAdjunction (gmTorsorπ L)).homEquiv
      (obj L (-1)) (gmTorsorStructureModule L)).symm
    (degreeInclude L (-1) ≫ gmTorsorπ_laurentToPushforward L)

/-- The reverse comparison `𝒪_T ⟶ q^* L` obtained by pulling back the
evaluation coevaluation of `L^{⊗ -1}` and contracting the resulting tensor
factor against `gmTorsorDegreeNegOneHom`. -/
noncomputable def gmTorsorTrivInv (L : X.Modules) [isInvertibleObject L] :
    𝟙_ (gmTorsor L).Modules ⟶ (pullback (gmTorsorπ L)).obj L :=
  (pullbackMonoidalUnitIso (gmTorsorπ L)).inv ≫
    (pullback (gmTorsorπ L)).map (evaluationIso L).inv ≫
      pullbackTensorOplax (gmTorsorπ L) L (obj L (-1)) ≫
        ((pullback (gmTorsorπ L)).obj L ◁
          (gmTorsorDegreeNegOneHom L ≫
            (gmTorsorStructureModuleIsoTensorUnit L).hom)) ≫
          (ρ_ ((pullback (gmTorsorπ L)).obj L)).hom

/-- The tautological trivialization `α : q^* L ≅ 𝒪_T`. -/
noncomputable def gmTorsorTriv (L : X.Modules) [isInvertibleObject L] :
    (pullback (gmTorsorπ L)).obj L ≅ 𝟙_ (gmTorsor L).Modules where
  hom := gmTorsorTrivHom L ≫ (gmTorsorStructureModuleIsoTensorUnit L).hom
  inv := gmTorsorTrivInv L
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `gmTorsorTriv` is the adjunct of degree-one insertion,
composed with the canonical identification of the commutative structure module
with `𝒪_T`. -/
theorem gmTorsorTriv_hom (L : X.Modules) [isInvertibleObject L] :
    (gmTorsorTriv L).hom =
      gmTorsorTrivHom L ≫ (gmTorsorStructureModuleIsoTensorUnit L).hom :=
  rfl

/-- Pullback of an invertible module along a morphism of algebraic spaces remains
invertible. -/
instance instIsInvertibleObject_pullback {Y : AlgebraicSpace S} (f : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] :
    isInvertibleObject ((pullback f).obj L) :=
  sorry

/-- Pullback of an invertible module along the `G_m`-torsor remains invertible. -/
instance instIsInvertibleObject_pullback_gmTorsorπ (L : X.Modules)
    [isInvertibleObject L] :
    isInvertibleObject ((pullback (gmTorsorπ L)).obj L) :=
  instIsInvertibleObject_pullback (gmTorsorπ L) L

/-- The structure morphism of the `G_m`-torsor of an invertible module is
surjective. -/
instance instSurjective_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    Surjective (gmTorsorπ L) :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is
smooth. -/
instance instSmooth_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    Smooth (gmTorsorπ L) :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is affine. -/
instance instAffine_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    Affine (gmTorsorπ L) :=
  instAffine_relativeSpecπ (invertibleLaurentAlgebra L)

/-- The structure morphism of the `G_m`-torsor of an invertible module has
relative dimension `1`. -/
instance instRelativeDimension_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    RelativeDimension (gmTorsorπ L) 1 :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is flat. -/
instance instFlat_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    Flat (gmTorsorπ L) :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is locally
of finite type. -/
instance instLocallyOfFiniteType_gmTorsorπ (L : X.Modules)
    [isInvertibleObject L] :
    LocallyOfFiniteType (gmTorsorπ L) :=
  sorry

/-- The structure morphism of the `G_m`-torsor of an invertible module is
quasi-separated. -/
instance instQuasiSeparated_gmTorsorπ (L : X.Modules) [isInvertibleObject L] :
    QuasiSeparated (gmTorsorπ L) :=
  sorry

/-- Composition of the `G_m`-torsor projection with a quasi-separated morphism
remains quasi-separated. -/
instance instQuasiSeparated_gmTorsorπ_comp {B : AlgebraicSpace S}
    (f : X ⟶ B) (L : X.Modules) [isInvertibleObject L] [QuasiSeparated f] :
    QuasiSeparated (gmTorsorπ L ≫ f) :=
  quasiSeparated_comp (gmTorsorπ L) f

/-- Composition of the `G_m`-torsor projection with a locally finite type
morphism remains locally of finite type. -/
instance instLocallyOfFiniteType_gmTorsorπ_comp {B : AlgebraicSpace S}
    (f : X ⟶ B) (L : X.Modules) [isInvertibleObject L]
    [LocallyOfFiniteType f] :
    LocallyOfFiniteType (gmTorsorπ L ≫ f) :=
  locallyOfFiniteType_comp (gmTorsorπ L) f

/-- Composition of the `G_m`-torsor projection with a flat morphism remains
flat. -/
instance instFlat_gmTorsorπ_comp {B : AlgebraicSpace S} (f : X ⟶ B)
    (L : X.Modules) [isInvertibleObject L] [Flat f] :
    Flat (gmTorsorπ L ≫ f) :=
  sorry


/-- The `G_m`-torsor of an invertible module on a decent algebraic space is
decent. -/
instance instIsDecent_gmTorsor (L : X.Modules) [isInvertibleObject L]
    [IsDecent X] : IsDecent (gmTorsor L) :=
  sorry

/-- Inverse image of an integral closed subspace along the `G_m`-torsor remains
integral. -/
instance instIsIntegral_inverseImage_gmTorsorπ (L : X.Modules)
    [isInvertibleObject L] (Z : ClosedSubspace X) [IsIntegral Z.X] :
    IsIntegral (Z.inverseImage (gmTorsorπ L)).X :=
  sorry

/-- Component at an actual elementary neighbourhood of the cocone inducing
`henselianMap`, using pointed neighbourhoods over the torsor projection. -/
noncomputable def henselianMap_ι_app (L : X.Modules) [isInvertibleObject L]
    [IsDecent X] (ξ : Points X) (ξ' : Points (gmTorsor L))
    (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
      IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ})))
    (U : EtaleNeighborhood.Elementary X ξ) :
    (EtaleNeighborhood.Elementary.sections X ξ).obj (ULiftHom.objUp (op U)) ⟶
      henselianLocalRingCat (gmTorsor L) ξ' :=
  HenselianFunctoriality.component (gmTorsorπ L) ξ' ξ hξ'.1 U

/-- The functoriality map of Decent Spaces Remark 68.11.11, constructed from
actual pointed elementary neighbourhoods and their global-section colimit. -/
noncomputable def henselianMap (L : X.Modules) [isInvertibleObject L]
    [IsDecent X] (ξ : Points X) (ξ' : Points (gmTorsor L))
    (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
      IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ}))) :
    henselianLocalRing X ξ →+* henselianLocalRing (gmTorsor L) ξ' :=
  HenselianFunctoriality.map (gmTorsorπ L) ξ' ξ hξ'.1

/-- The comparison of henselian local rings along the `G_m`-torsor is a local
homomorphism. -/
instance instIsLocalHom_henselianMap (L : X.Modules) [isInvertibleObject L]
    [IsDecent X] (ξ : Points X) (ξ' : Points (gmTorsor L))
    (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
      IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ}))) :
    IsLocalHom (henselianMap L ξ ξ' hξ') :=
  sorry

/-- The residue-field map induced by `henselianMap`. -/
noncomputable def henselianResidueFieldMap (L : X.Modules)
    [isInvertibleObject L] [IsDecent X] (ξ : Points X)
    (ξ' : Points (gmTorsor L))
    (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
      IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ}))) :
    ResidueField (henselianLocalRing X ξ) →+*
      ResidueField (henselianLocalRing (gmTorsor L) ξ') :=
  ResidueField.map (henselianMap L ξ ξ' hξ')

/-- `henselianResidueFieldMap` is `ResidueField.map` of `henselianMap`. -/
theorem henselianResidueFieldMap_eq (L : X.Modules) [isInvertibleObject L]
    [IsDecent X] (ξ : Points X) (ξ' : Points (gmTorsor L))
    (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
      IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ}))) :
    henselianResidueFieldMap L ξ ξ' hξ' =
      ResidueField.map (henselianMap L ξ ξ' hξ') :=
  rfl

/-- The comparison of henselian local rings along the `G_m`-torsor is flat. -/
theorem gmTorsorπ_henselianMap_flat (L : X.Modules) [isInvertibleObject L]
    [IsDecent X] (ξ : Points X) (ξ' : Points (gmTorsor L))
    (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
      IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ}))) :
    RingHom.Flat (henselianMap L ξ ξ' hξ') :=
  sorry

/-- The maximal ideal of `𝒪_{T,ξ'}^h` is generated by the image of `m_ξ^h`. -/
theorem gmTorsorπ_henselianMap_maximalIdeal (L : X.Modules)
    [isInvertibleObject L] [IsDecent X] (ξ : Points X)
    (ξ' : Points (gmTorsor L))
    (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
      IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ}))) :
    maximalIdeal (henselianLocalRing (gmTorsor L) ξ') =
      (maximalIdeal (henselianLocalRing X ξ)).map (henselianMap L ξ ξ' hξ') :=
  sorry

/-- The residue-field extension along `henselianMap` is purely transcendental. -/
theorem gmTorsorπ_henselianMap_isPurelyTranscendental (L : X.Modules)
    [isInvertibleObject L] [IsDecent X] (ξ : Points X)
    (ξ' : Points (gmTorsor L))
    (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
      IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ}))) :
    (ResidueField.map (henselianMap L ξ ξ' hξ')).IsPurelyTranscendental :=
  sorry

/-- An actual Laurent algebra map gives an underlying map into the direct image of the unit module. -/
noncomputable def laurentAlgebraToUnitUnderlying {Y : AlgebraicSpace S}
    (h : Y ⟶ X) (L : X.Modules) [isInvertibleObject L]
    (α : (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commRingStructureSheafMap h)) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj (invertibleLaurentModule L) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
        ((pushforward h).obj (𝟙_ Y.Modules)) :=
  restrictionUnitCarrierToForget (invertibleLaurentStructureMap L) ≫
    ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})) ⋙
      sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).map α.right ≫
    (commRingPushforwardForgetTypeIso h).hom.app (commRingStructureSheaf Y) ≫
    (typePushforward h).map
      (forgetToStructureUnitCarrier Y ≫
        (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).map
          (structureModuleIsoTensorUnit Y).hom) ≫
    (ModulePushforward.forgetIso (ringedToposHom h)).inv.app (𝟙_ Y.Modules)

/-- The module map carried by an actual Laurent algebra map. -/
noncomputable def laurentAlgebraToUnitPushforward {Y : AlgebraicSpace S}
    (h : Y ⟶ X) (L : X.Modules) [isInvertibleObject L]
    (α : (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commRingStructureSheafMap h)) :
    invertibleLaurentModule L ⟶ (pushforward h).obj (𝟙_ Y.Modules) :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf X)
    (laurentAlgebraToUnitUnderlying h L α) (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- Adjunction sends degree-one evaluation of an algebra map to its frame homomorphism. -/
noncomputable def laurentAlgebraFrameHom {Y : AlgebraicSpace S}
    (h : Y ⟶ X) (L : X.Modules) [isInvertibleObject L]
    (α : (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commRingStructureSheafMap h)) :
    (pullback h).obj L ⟶ 𝟙_ Y.Modules :=
  ((pullbackPushforwardAdjunction h).homEquiv L (𝟙_ Y.Modules)).symm
    (degreeIncludeOne L ≫ laurentAlgebraToUnitPushforward h L α)

/-- Section values of actual algebra maps whose degree-one adjunct is the supplied frame. -/
def IsFrameClassifyingSection {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U)
    (s : ((commRingPushforward h).obj (commRingStructureSheaf Y)).obj.obj U) : Prop :=
  ∃ α : (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commRingStructureSheafMap h),
    laurentAlgebraFrameHom h L α = frame.hom ∧
      ((InducedCategory.Hom.hom α.right).app U).hom a = s

/-- Evaluate using an actual in-range algebra-map witness, never a witness extracted from admitted surjectivity. -/
noncomputable def frameClassifyingSection {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U) :
    ((commRingPushforward h).obj (commRingStructureSheaf Y)).obj.obj U := by
  classical
  exact if hs : ∃ s, IsFrameClassifyingSection h L frame U a s then Classical.choose hs else 0

/-- Local Laurent evaluation at the actual frame glues uniquely, so its section family is in range. -/
theorem frameClassifyingSection_inRange {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U) :
    ∃ s, IsFrameClassifyingSection h L frame U a s := sorry

/-- The selected value is supplied by an actual algebra map with the specified degree-one frame. -/
theorem frameClassifyingSection_spec {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (a : (invertibleLaurentSheaf L).obj.obj U) :
    IsFrameClassifyingSection h L frame U a (frameClassifyingSection h L frame U a) := by
  classical
  unfold frameClassifyingSection
  split_ifs with hs
  · exact Classical.choose_spec hs
  · exact False.elim (hs (frameClassifyingSection_inRange h L frame U a))

/-- The section ring map classified by the supplied frame, evaluating every Laurent degree. -/
noncomputable def frameClassifyingRingHom {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (invertibleLaurentSheaf L).obj.obj U →+*
      ((commRingPushforward h).obj (commRingStructureSheaf Y)).obj.obj U where
  toFun := frameClassifyingSection h L frame U
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- A frame, rather than a base morphism alone, determines its Laurent algebra homomorphism. -/
noncomputable def invertibleLaurentClassifyingMap {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules) :
    (invertibleLaurentAlgebra L).obj ⟶ Under.mk (commRingStructureSheafMap h) :=
  Under.homMk
    ⟨{ app := fun U ↦ @CommRingCat.ofHom ((invertibleLaurentSheaf L).obj.obj U)
         (((commRingPushforward h).obj (commRingStructureSheaf Y)).obj.obj U)
         (inferInstanceAs (CommRing ((invertibleLaurentSheaf L).obj.obj U)))
         (inferInstanceAs (CommRing (((commRingPushforward h).obj (commRingStructureSheaf Y)).obj.obj U)))
         (frameClassifyingRingHom h L frame U)
       naturality := sorry }⟩ sorry

/-- The test-scheme classifier consumes the actual pullback trivialization. -/
noncomputable def invertibleLaurentToRelativeSpectrumTarget {T : Over S}
    (g : ofOver T ⟶ X) (L : X.Modules) [isInvertibleObject L]
    (frame : (pullback g).obj L ≅ 𝟙_ (ofOver T).Modules) :
    (invertibleLaurentAlgebra L).obj ⟶ relativeSpectrumTarget g :=
  invertibleLaurentClassifyingMap g L frame

/-- Pull an actual frame back along a test morphism, retaining the canonical composition and unit comparisons. -/
noncomputable def pullbackFrame {Y Z : AlgebraicSpace S} (h : Y ⟶ X) (t : Z ⟶ Y)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules) :
    (pullback (t ≫ h)).obj L ≅ 𝟙_ Z.Modules :=
  (pullbackComp t h).symm.app L ≪≫ (pullback t).mapIso frame ≪≫ pullbackMonoidalUnitIso t

/-- The morphism to the torsor classified by an actual trivialization of the pulled-back line. -/
noncomputable def gmTorsorLift {Y : AlgebraicSpace S} (h : Y ⟶ X)
    (L : X.Modules) [isInvertibleObject L] (frame : (pullback h).obj L ≅ 𝟙_ Y.Modules) :
    Y ⟶ gmTorsor L where
  app T := TypeCat.ofHom fun y ↦
    let t : ofOver T.unop ⟶ Y := yonedaEquiv.symm y
    relativeSpectrumPairMk (t ≫ h)
      (invertibleLaurentToRelativeSpectrumTarget (t ≫ h) L (pullbackFrame h t L frame))
  naturality := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
