module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap94.Lemma_94_16_1_QuotientMap
public import stacks_project.Chap94.Remark_94_16_3_Quotient
public import stacks_project.Chap96.Lemma_96_13_2
public import stacks_project.Chap96.Proposition_96_14_3
public import stacks_project.Chap101.Lemma_101_17_5
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap103.Definition_103_17_2_Coh
public import stacks_project.Chap103.Lemma_103_17_8_Coh

/-!
# Coherent modules via a flat locally of finite presentation presentation

A surjective, flat, locally of finite presentation morphism from an algebraic
space to a locally Noetherian algebraic stack induces an equivalence on
quasi-coherent modules with the kernel-pair groupoid, and this equivalence
restricts to coherent modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable [AlgebraicStack X] [IsLocallyNoetherian X]

/-- The inclusion of coherent `𝒪_X`-modules into quasi-coherent `𝒪_X`-modules. -/
def Coh.toQCoh : AlgebraicStack.Coh X ⥤ GroupoidsOver.QCoh X :=
  (GroupoidsOver.quasiCoherentModuleProperty X).lift
    (AlgebraicStack.Coh.inclusion X) (fun _ ↦ sorry)

/-- The underlying sheaf of `toQCoh` is the inclusion of `Coh(𝒪_X)`. -/
theorem Coh.toQCoh_obj (F : AlgebraicStack.Coh X) :
    ((Coh.toQCoh).obj F).obj = F.obj :=
  sorry

variable (U : AlgebraicSpace S) (f : U.toGroupoids ⟶ X)
variable [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
variable [Groupoids.Hom.LocallyOfFinitePresentation f]

/-- A locally of finite presentation 1-morphism from an algebraic space to an
algebraic stack is locally of finite type. -/
instance locallyOfFiniteType_of_locallyOfFinitePresentation :
    LocallyOfFiniteType f :=
  let _ := ‹Groupoids.Hom.LocallyOfFinitePresentation f›
  sorry

/-- The object space of the kernel-pair groupoid of a surjective flat locally of
finite presentation atlas of a locally Noetherian algebraic stack is locally
Noetherian. -/
instance groupoid_objectSpace_isLocallyNoetherian :
    AlgebraicSpace.IsLocallyNoetherian
      (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)).U.left :=
  let _ := locallyOfFiniteType_of_locallyOfFinitePresentation U f
  let _ := LocallyOfFiniteType.isLocallyNoetherian f
  sorry

/-- Pullback of quasi-coherent modules along `fCan f hU` is an equivalence when
`f` is a surjective flat locally of finite presentation atlas. -/
instance qCohPullback_fCan_isEquivalence :
    (GroupoidsOver.QCoh.pullback
        (fCan f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))).IsEquivalence :=
  let _ := fCan_isEquivalence_of_flat f
    (IsRepresentableByAlgebraicSpace.of_toGroupoids U)
  sorry

/-- The composite equivalence `QCoh(𝒪_X) ≌ QCoh(U, R, s, t, c)` obtained from
pullback along `fCan` and the quotient-stack comparison `toGroupoidEquivalence`. -/
def qCohEquivalence :
    GroupoidsOver.QCoh X ≌
      (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)).QCoh :=
  let _ := fCan_isEquivalence_of_flat f
    (IsRepresentableByAlgebraicSpace.of_toGroupoids U)
  (GroupoidsOver.QCoh.pullback
      (fCan f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))).asEquivalence.trans
    (GroupoidsOver.QCoh.toGroupoidEquivalence
      (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)))

/-- The forward functor of `qCohEquivalence` is pullback along `fCan` followed by
`toGroupoid`. -/
theorem qCohEquivalence_functor :
    (qCohEquivalence U f).functor =
      GroupoidsOver.QCoh.pullback
          (fCan f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)) ⋙
        GroupoidsOver.QCoh.toGroupoid
          (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)) :=
  sorry

/-- The inverse functor of `qCohEquivalence` is `fromGroupoid` followed by the
inverse of pullback along `fCan`. -/
theorem qCohEquivalence_inverse :
    (qCohEquivalence U f).inverse =
      (GroupoidsOver.QCoh.toGroupoidEquivalence
            (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))).inverse ⋙
        (GroupoidsOver.QCoh.pullback
            (fCan f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))).inv :=
  sorry

/-- An `𝒪_X`-module is coherent if and only if its image under `qCohEquivalence`
is a coherent equivariant module on the kernel-pair groupoid. -/
theorem Coh.isCoherent_iff_groupoid (F : GroupoidsOver.QCoh X) :
    AlgebraicStack.IsCoherent F.obj ↔
      GroupoidAlgebraicSpace.IsCoherent ((qCohEquivalence U f).functor.obj F) :=
  sorry

/-- The forward functor sending a coherent `𝒪_X`-module to the corresponding
coherent equivariant module on the kernel-pair groupoid. -/
def Coh.toGroupoid :
    AlgebraicStack.Coh X ⥤
      GroupoidAlgebraicSpace.Coh
        (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)) :=
  (GroupoidAlgebraicSpace.coherentModuleProperty
      (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))).lift
    (Coh.toQCoh ⋙ (qCohEquivalence U f).functor) (fun _ ↦ sorry)

/-- The underlying equivariant module of `Coh.toGroupoid` is the image under
`qCohEquivalence`. -/
theorem Coh.toGroupoid_obj (F : AlgebraicStack.Coh X) :
    ((Coh.toGroupoid U f).obj F).obj = (qCohEquivalence U f).functor.obj (Coh.toQCoh.obj F) :=
  sorry

/-- The inverse functor sending a coherent equivariant module on the kernel-pair
groupoid to a coherent `𝒪_X`-module. -/
def Coh.fromGroupoid :
    GroupoidAlgebraicSpace.Coh
        (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)) ⥤
      AlgebraicStack.Coh X :=
  (AlgebraicStack.coherentModuleProperty X).lift
    (GroupoidAlgebraicSpace.Coh.inclusion
        (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)) ⋙
      (qCohEquivalence U f).inverse ⋙ GroupoidsOver.QCoh.inclusion X)
    (fun _ ↦ sorry)

/-- The underlying sheaf of `Coh.fromGroupoid` is the image under the inverse of
`qCohEquivalence`. -/
theorem Coh.fromGroupoid_obj
    (A : GroupoidAlgebraicSpace.Coh
      (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))) :
    ((Coh.fromGroupoid U f).obj A).obj =
      ((qCohEquivalence U f).inverse.obj A.obj).obj :=
  sorry

/-- The unit isomorphism of the restricted coherent-module equivalence, with
component morphisms those of `qCohEquivalence`. -/
def Coh.groupoidEquivalence_unitIso :
    𝟭 (AlgebraicStack.Coh X) ≅ Coh.toGroupoid U f ⋙ Coh.fromGroupoid U f :=
  NatIso.ofComponents
    (fun F ↦
      (AlgebraicStack.coherentModuleProperty X).isoMk
        ((GroupoidsOver.QCoh.inclusion X).mapIso
          ((qCohEquivalence U f).unitIso.app (Coh.toQCoh.obj F))))
    sorry

/-- The counit isomorphism of the restricted coherent-module equivalence, with
component morphisms those of `qCohEquivalence`. -/
def Coh.groupoidEquivalence_counitIso :
    Coh.fromGroupoid U f ⋙ Coh.toGroupoid U f ≅
      𝟭 (GroupoidAlgebraicSpace.Coh
          (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))) :=
  NatIso.ofComponents
    (fun A ↦
      (GroupoidAlgebraicSpace.coherentModuleProperty
          (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U))).isoMk
        ((qCohEquivalence U f).counitIso.app A.obj))
    sorry

/-- The equivalence `Coh(𝒪_X) ≌ Coh(U, R, s, t, c)` induced by the quasi-coherent
presentation equivalence of a surjective flat locally of finite presentation
atlas. -/
def Coh.groupoidEquivalence :
    AlgebraicStack.Coh X ≌
      GroupoidAlgebraicSpace.Coh
        (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)) :=
  CategoryTheory.Equivalence.mk (Coh.toGroupoid U f) (Coh.fromGroupoid U f)
    (Coh.groupoidEquivalence_unitIso U f) (Coh.groupoidEquivalence_counitIso U f)

/-- The forward functor of `groupoidEquivalence` is `Coh.toGroupoid`. -/
theorem Coh.groupoidEquivalence_functor :
    (Coh.groupoidEquivalence U f).functor = Coh.toGroupoid U f :=
  sorry

/-- The inverse functor of `groupoidEquivalence` is `Coh.fromGroupoid`. -/
theorem Coh.groupoidEquivalence_inverse :
    (Coh.groupoidEquivalence U f).inverse = Coh.fromGroupoid U f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
