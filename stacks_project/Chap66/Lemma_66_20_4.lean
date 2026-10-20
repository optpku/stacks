/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Support.Properties
import StacksCheckRecall

/-!
# Support of local sections of an abelian sheaf on `X_étale`

The support of a local section is closed in `|U|`, cannot grow under addition or
sheaf maps, and assembles the support of the sheaf as the union of images in `|X|`.
Surjective maps reverse-include supports; injective maps include them.

The printed closedness statement refers to `|X|`, but the preceding definition and the
proof place the support of a local section in `|U|`. Addition likewise compares sections
over the same arbitrary étale object `U`, as in the proof by restriction to `U_Zar`.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.20.4 (1): the support of a local section is closed in its domain `|U|`. -/
@[stacks 04KB] #check (AlgebraicGeometry.AlgebraicSpace.isClosed_abelianSheafSectionSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)),
    IsClosed (abelianSheafSectionSupport F U σ : Set U.left.left))

/- Lemma 66.20.4 (2): the support of a sum is contained in the union of the supports. -/
@[stacks 04KB] #check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSectionSupport_add_subset :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : smallEtaleSite X) (σ σ' : F.obj.obj (op U)),
    (abelianSheafSectionSupport F U (σ + σ') : Set U.left.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left.left) ∪
        (abelianSheafSectionSupport F U σ' : Set U.left.left))

/- Lemma 66.20.4 (3): a sheaf morphism cannot enlarge the support of a local section. -/
@[stacks 04KB] #check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSectionSupport_map_subset :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (U : smallEtaleSite X) (σ : F.obj.obj (op U)),
    (abelianSheafSectionSupport G U (φ.hom.app (op U) σ) : Set U.left.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left.left))

/- Lemma 66.20.4 (4): sheaf support is the union of images of local section supports. -/
@[stacks 04KB] #check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSupport_eq_iUnion_sectionSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    abelianSheafSupport F =
      ⋃ (U : smallEtaleSite X) (σ : F.obj.obj (op U)),
        Points.mapOfOver U.hom '' (abelianSheafSectionSupport F U σ : Set U.left.left))

/- Lemma 66.20.4 (5): a surjective sheaf map decreases support. -/
@[stacks 04KB] #check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSupport_subset_of_epi :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ],
    abelianSheafSupport G ⊆ abelianSheafSupport F)

/- Lemma 66.20.4 (6): an injective sheaf map includes source support in target support. -/
@[stacks 04KB] #check (AlgebraicGeometry.AlgebraicSpace.abelianSheafSupport_subset_of_mono :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Mono φ],
    abelianSheafSupport F ⊆ abelianSheafSupport G)

end AlgebraicGeometry.AlgebraicSpace
