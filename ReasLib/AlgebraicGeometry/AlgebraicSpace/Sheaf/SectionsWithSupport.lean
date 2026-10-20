/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.InjectivePushforward

/-!
# Sections with support on a closed subspace

Sections supported on a closed subspace form the kernel of restriction to its
open complement. Viewed on the closed subspace, they preserve injective abelian
sheaves. Higher sections with support vanish on injective direct images.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `rightDerived`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

/-- The endofunctor of abelian sheaves consisting of sections supported on the image
of a closed immersion, defined as the kernel of restriction to its open complement. -/
def sectionsWithSupportOn
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  let U := OpenSubspace.fromOpens
    ⟨(ClosedSubspace.ofι i).pointsSetᶜ,
      (ClosedSubspace.isClosed_pointsSet (ClosedSubspace.ofι i)).isOpen_compl⟩
  kernel (sheafAdjunction AddCommGrpCat.{u + 1} U.ι).unit

/-- The canonical inclusion of the supported subsheaf into the ambient abelian sheaf. -/
def sectionsWithSupportOnι
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    sectionsWithSupportOn i ⟶ 𝟭 (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  let U := OpenSubspace.fromOpens
    ⟨(ClosedSubspace.ofι i).pointsSetᶜ,
      (ClosedSubspace.isClosed_pointsSet (ClosedSubspace.ofι i)).isOpen_compl⟩
  kernel.ι (sheafAdjunction AddCommGrpCat.{u + 1} U.ι).unit

/-- Sections supported on the image of a closed immersion, viewed as an abelian sheaf
on the small étale site of the closed subspace. -/
def sectionsWithSupport
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1} :=
  sectionsWithSupportOn i ⋙ sheafInverseImage AddCommGrpCat.{u + 1} i

/-- A section belongs to the supported subsheaf exactly when its restriction to the
open complement vanishes. -/
theorem mem_range_sectionsWithSupportOnι_iff
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (V : smallEtaleSite X)
    (σ : F.obj.obj (Opposite.op V)) :
    σ ∈ Set.range
        ((((sectionsWithSupportOnι i).app F).hom.app (Opposite.op V)) :
          ((sectionsWithSupportOn i).obj F).obj.obj (Opposite.op V) →
            F.obj.obj (Opposite.op V)) ↔
      (let U := OpenSubspace.fromOpens
         ⟨(ClosedSubspace.ofι i).pointsSetᶜ,
           (ClosedSubspace.isClosed_pointsSet (ClosedSubspace.ofι i)).isOpen_compl⟩
       (((sheafAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app F).hom.app
         (Opposite.op V)) σ = 0) := sorry

/-- The ordinary inverse-image/direct-image unit is an isomorphism on the supported
subsheaf of an abelian sheaf. -/
instance sectionsWithSupportOn_unit_isIso
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    IsIso ((sheafAdjunction AddCommGrpCat.{u + 1} i).unit.app
      ((sectionsWithSupportOn i).obj F)) := sorry

/-- Sections supported on a closed subspace preserve injective abelian sheaves on
small étale sites. -/
instance sectionsWithSupport_preservesInjectiveObjects
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    (sectionsWithSupport i).PreservesInjectiveObjects := sorry

/-- The sheaf of sections of an injective abelian sheaf supported on a closed subspace
is injective on the small étale site of that subspace. -/
instance sectionsWithSupport_injective
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (ℐ : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) [Injective ℐ] :
    Injective ((sectionsWithSupport i).obj ℐ) :=
  Functor.injective_obj (sectionsWithSupport i) ℐ

/-- For a closed immersion of algebraic spaces, the positive right-derived functors of
sections with support vanish on the direct image of an injective abelian sheaf.
The sections-with-support functor is specified as a right adjoint to direct image. -/
theorem closedImmersion_higherSectionsWithSupport_isZero
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjunction : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [sectionsWithSupport.Additive]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (G : Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) [Injective G]
    (p : ℕ) (hp : 0 < p) :
    IsZero ((sectionsWithSupport.rightDerived p).obj
      ((sheafPushforward AddCommGrpCat.{u + 1} i).obj G)) := sorry

end AlgebraicGeometry.AlgebraicSpace
