/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Coherent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair.Quasicoherent

/-!
# Coherent modules on flat groupoid presentations

The quasi-coherent presentation equivalence of a locally Noetherian algebraic
stack preserves and reflects coherence and restricts to coherent modules.
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
variable (U : AlgebraicSpace S) (f : U.toGroupoids ⟶ X)
variable [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
variable [Groupoids.Hom.LocallyOfFinitePresentation f]

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
