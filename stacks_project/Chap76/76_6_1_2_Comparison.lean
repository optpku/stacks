/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_13_5_Adjunction
public import stacks_project.Chap76.Definition_76_6_5_Conormal
public import stacks_project.Chap76.Definition_76_6_5_Symmetric
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.CommRingAdjunction
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Symmetric-to-total comparison for conormal algebras of immersions

The degree-one classes in the coborder associated graded induce a canonical morphism of
quasi-coherent `𝒪_Z`-algebras from the symmetric algebra of the conormal sheaf to the total
conormal algebra of an immersion of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory Opposite
open CategoryTheory.Functor
open AlgebraicGeometry
open SheafOfModules.RingedSite
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Spaces-étale sheaves of commutative rings compose with the forgetful functor to rings. -/
instance spacesEtaleTopology_hasSheafCompose_forget₂_commRing (X : AlgebraicSpace S) :
    (spacesEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- Forgetting commutativity commutes with small étale direct image of commutative-ring
sheaves. -/
def commRingPushforwardForget₂Iso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingPushforward f ⋙
        sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        ringPushforward f :=
  commRingPushforwardForgetIso f

/-- Forgetting all the way to types after commutative-ring pushforward recovers type-valued
direct image of the underlying type sheaf. -/
def commRingPushforwardForgetTypeIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingPushforward f ⋙
        sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
          sheafCompose (smallEtaleTopology Y) (forget RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        sheafCompose (smallEtaleTopology X) (forget RingCat.{u}) ⋙
          typePushforward f :=
  commRingPushforwardUnderlyingIso f ≪≫ Functor.associator _ _ _

namespace ConormalAlgebra

variable {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- The `𝒪_Z`-module underlying the total conormal algebra. -/
abbrev totalUnderlyingModule :=
  (restrictionAlong (total i).obj.hom).obj
    (unitModule (smallEtaleTopology Z) (QcAlgebraUnder.sheaf (total i)))

/-- `totalUnderlyingModule i` is restriction of scalars of the unit module of the total
conormal algebra. -/
theorem totalUnderlyingModule_eq :
    totalUnderlyingModule i =
      (restrictionAlong (total i).obj.hom).obj
        (unitModule (smallEtaleTopology Z) (QcAlgebraUnder.sheaf (total i))) :=
  rfl

/-- The adjunct of `totalInr`, sending the coborder associated graded into the pushforward of
the total conormal algebra sheaf. -/
def totalInrAdjunct :
    coborderGradeSheaf i ⟶
      (commRingPushforward (IsImmersion.liftCoborder i)).obj (totalSheaf i) :=
  (commRingInverseImageAdjunction (IsImmersion.liftCoborder i)).homEquiv _ _ (totalInr i)

/-- `totalInrAdjunct` is the inverse-image/direct-image adjunct of `totalInr`. -/
theorem totalInrAdjunct_eq :
    totalInrAdjunct i =
      (commRingInverseImageAdjunction (IsImmersion.liftCoborder i)).homEquiv _ _
        (totalInr i) :=
  rfl

/-- The structure map from the coborder structure sheaf to the direct image of the total
conormal algebra. -/
def coborderToPushforwardTotal :
    commRingStructureSheaf (Hom.coborder i) ⟶
      (commRingPushforward (IsImmersion.liftCoborder i)).obj (totalSheaf i) :=
  coborderStructureMap i ≫ totalInrAdjunct i

/-- `coborderToPushforwardTotal` is the coborder associated-graded structure map followed by
the adjunct of `totalInr`. -/
theorem coborderToPushforwardTotal_eq :
    coborderToPushforwardTotal i = coborderStructureMap i ≫ totalInrAdjunct i :=
  rfl

/-- Direct image of the total conormal algebra, regarded as an `𝒪_{X \ ∂Z}`-module by
restriction of scalars along `coborderToPushforwardTotal`. -/
abbrev totalPushforwardUnitModule :=
  (restrictionAlong (coborderToPushforwardTotal i)).obj
    (unitModule (smallEtaleTopology (Hom.coborder i))
      ((commRingPushforward (IsImmersion.liftCoborder i)).obj (totalSheaf i)))

/-- `totalPushforwardUnitModule i` is restriction of scalars of the unit module of the
pushed total conormal algebra. -/
theorem totalPushforwardUnitModule_eq :
    totalPushforwardUnitModule i =
      (restrictionAlong (coborderToPushforwardTotal i)).obj
        (unitModule (smallEtaleTopology (Hom.coborder i))
          ((commRingPushforward (IsImmersion.liftCoborder i)).obj
            (totalSheaf i))) :=
  rfl

/-- A local section of the coborder associated ideal sheaf lies in the ordinary kernel ideal of
the coborder structure map. -/
theorem idealSheafι_app_mem_sectionIdeal (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ)
    (x : (Hom.idealSheaf (IsImmersion.liftCoborder i)).val.obj U) :
    (Hom.idealSheafι (IsImmersion.liftCoborder i)).val.app U x ∈
      KernelIdeal.sectionIdeal (coborderKernelMap i) U :=
  sorry

/-- On an étale object of the coborder, the associated ideal sheaf maps to the restricted unit
of the pushed total conormal algebra by placing a section in degree one. -/
def coborderIdealToPushforwardTotalApp (U : (smallEtaleSite (Hom.coborder i))ᵒᵖ) :
    (Hom.idealSheaf (IsImmersion.liftCoborder i)).val.obj U ⟶
      (totalPushforwardUnitModule i).val.obj U :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom
      { toFun := fun x ↦
          (((InducedCategory.Hom.hom (totalInrAdjunct i)).app U).hom
            (((toSheafify (smallEtaleTopology (Hom.coborder i))
                  (coborderGradePresheaf i)).app U).hom
              (Ideal.AssociatedGraded.degreeOne
                ⟨(Hom.idealSheafι (IsImmersion.liftCoborder i)).val.app U x,
                  idealSheafι_app_mem_sectionIdeal i U x⟩)))
        map_zero' := sorry
        map_add' := sorry })
    (fun _ ↦ sorry)

/-- The coborder associated ideal sheaf maps to the restricted unit of the pushed total
conormal algebra by the degree-one associated-graded class. -/
def coborderIdealToPushforwardTotal :
    Hom.idealSheaf (IsImmersion.liftCoborder i) ⟶
      Modules.ofComm (totalPushforwardUnitModule i) where
  val :=
    { app := coborderIdealToPushforwardTotalApp i
      naturality := fun {_ _} _ ↦ sorry }

/-- The coborder ideal-square action vanishes on the degree-one map into the restricted unit of
the pushed total conormal algebra. -/
theorem coborderIdealToPushforwardTotal_vanishes :
    Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
          (Hom.idealSheaf (IsImmersion.liftCoborder i)) ≫
        coborderIdealToPushforwardTotal i =
      0 :=
  sorry

/-- The type-valued sheaf underlying the restricted unit module of a commutative-ring sheaf
maps to the ordinary forgetful type sheaf of that ring sheaf. -/
def restrictionUnitCarrierToForget
    {Y : AlgebraicSpace S} {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    (α : commRingStructureSheaf Y ⟶ A) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
        (Modules.ofComm ((restrictionAlong α).obj (unitModule (smallEtaleTopology Y) A))) ⟶
      (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj A) :=
  InducedCategory.homMk
    { app := fun U ↦ 𝟙 _
      naturality := fun {_ _} _ ↦ sorry }

/-- The ordinary forgetful type sheaf of a commutative-ring sheaf maps to the type-valued sheaf
underlying the restricted unit module of that ring sheaf. -/
def forgetToRestrictionUnitCarrier
    {Y : AlgebraicSpace S} {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    (α : commRingStructureSheaf Y ⟶ A) :
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).obj
        ((sheafCompose (smallEtaleTopology Y)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Y)).obj
        (Modules.ofComm ((restrictionAlong α).obj (unitModule (smallEtaleTopology Y) A))) :=
  InducedCategory.homMk
    { app := fun U ↦ 𝟙 _
      naturality := fun {_ _} _ ↦ sorry }

/-- Identifying the restricted unit of `j_*` of the total conormal algebra with the module
pushforward of the total conormal module. -/
def totalPushforwardUnitTypeToPushforward :
    (Sheaf.InternalModule.ToInternal.underlying
          (structureSheaf (Hom.coborder i))).obj
        (Modules.ofComm (totalPushforwardUnitModule i)) ⟶
      (Sheaf.InternalModule.ToInternal.underlying
          (structureSheaf (Hom.coborder i))).obj
        ((Modules.pushforward (IsImmersion.liftCoborder i)).obj
          (Modules.ofComm (totalUnderlyingModule i))) :=
  restrictionUnitCarrierToForget (coborderToPushforwardTotal i) ≫
    (commRingPushforwardForgetTypeIso (IsImmersion.liftCoborder i)).hom.app (totalSheaf i) ≫
      (typePushforward (IsImmersion.liftCoborder i)).map
        (forgetToRestrictionUnitCarrier (total i).obj.hom) ≫
      (ModulePushforward.forgetIso (ringedToposHom (IsImmersion.liftCoborder i))).inv.app
        (Modules.ofComm (totalUnderlyingModule i))

/-- The restricted unit of `j_*` of the total conormal algebra, recast as the module
pushforward of the total conormal module. -/
def totalPushforwardUnitToPushforward :
    Modules.ofComm (totalPushforwardUnitModule i) ⟶
      (Modules.pushforward (IsImmersion.liftCoborder i)).obj
        (Modules.ofComm (totalUnderlyingModule i)) :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf (Hom.coborder i))
    (totalPushforwardUnitTypeToPushforward i) (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- On the coborder closed immersion, the successive quotient `I / I²` maps to the pushforward
of the total conormal algebra by descending the degree-one associated-graded map. -/
def coborderDegreeOne :
    Modules.quotientByIdeal (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i)) ⟶
      (Modules.pushforward (IsImmersion.liftCoborder i)).obj
        (Modules.ofComm (totalUnderlyingModule i)) :=
  cokernel.desc
      (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i)))
      (coborderIdealToPushforwardTotal i)
      (coborderIdealToPushforwardTotal_vanishes i) ≫
    totalPushforwardUnitToPushforward i

/-- `coborderDegreeOne` is the cokernel descent of the coborder degree-one map, identified with
the module pushforward of the total conormal algebra. -/
theorem coborderDegreeOne_eq :
    coborderDegreeOne i =
      cokernel.desc
          (Modules.idealAction (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
            (Hom.idealSheaf (IsImmersion.liftCoborder i)))
          (coborderIdealToPushforwardTotal i)
          (coborderIdealToPushforwardTotal_vanishes i) ≫
        totalPushforwardUnitToPushforward i :=
  rfl

/-- The conormal sheaf maps canonically to the module underlying the total conormal algebra by
placing cotangent classes in degree one. -/
def degreeOneToTotal :
    Modules.toComm (Hom.conormalSheaf i) ⟶ totalUnderlyingModule i where
  val :=
    (((Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).homEquiv
          (Modules.quotientByIdeal
            (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
            (Hom.idealSheaf (IsImmersion.liftCoborder i)))
          (Modules.ofComm (totalUnderlyingModule i))).symm
        (coborderDegreeOne i)).val

/-- `degreeOneToTotal` is the adjunct of the coborder degree-one comparison. -/
theorem degreeOneToTotal_eq :
    (degreeOneToTotal i).val =
      (((Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).homEquiv
          (Modules.quotientByIdeal
            (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
            (Hom.idealSheaf (IsImmersion.liftCoborder i)))
          (Modules.ofComm (totalUnderlyingModule i))).symm
        (coborderDegreeOne i)).val :=
  rfl

/-- The symmetric algebra of the conormal sheaf maps canonically to the total conormal
algebra. -/
def symmetricToTotal :
    SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i) ⟶ total i :=
  SymmetricAlgebra.lift (Hom.conormalSheaf i) (total i) (degreeOneToTotal i)

/-- `symmetricToTotal` is the symmetric-algebra lift of the degree-one inclusion of the
conormal sheaf. -/
theorem symmetricToTotal_eq :
    symmetricToTotal i =
      SymmetricAlgebra.lift (Hom.conormalSheaf i) (total i) (degreeOneToTotal i) :=
  rfl

/-- The symmetric-to-total comparison recovers `degreeOneToTotal` on degree-one generators. -/
theorem symmetricToTotal_comp_degreeOne (U : (smallEtaleSite Z)ᵒᵖ)
    (x : (Modules.toComm (Hom.conormalSheaf i)).val.obj U) :
    (SymmetricAlgebra.liftApp (Hom.conormalSheaf i) (total i) (degreeOneToTotal i) U).hom
        (_root_.SymmetricAlgebra.ι ((commRingStructureSheaf Z).obj.obj U)
          ((Modules.toComm (Hom.conormalSheaf i)).val.obj U) x) =
      (degreeOneToTotal i).val.app U x :=
  sorry

/-- In degree zero, the symmetric-to-total comparison is the identity on structure sheaves. -/
theorem symmetricToTotal_degreeZero :
    SymmetricAlgebra.structureMap (Hom.conormalSheaf i) ≫
        (symmetricToTotal i).hom.right =
      structureMap i :=
  sorry

/-- The underlying commutative-ring sheaf map of the canonical comparison
`Sym^*(C_{Z/X}) ⟶ C_{Z/X,*}` is locally surjective. -/
instance instIsLocallySurjective_symmetricToTotal :
    Sheaf.IsLocallySurjective (symmetricToTotal i).hom.right :=
  sorry

end ConormalAlgebra

end AlgebraicGeometry.AlgebraicSpace
