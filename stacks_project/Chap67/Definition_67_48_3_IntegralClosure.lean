/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_28_1_Hom
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_20_10_Pushforward
public import stacks_project.Chap67.Lemma_67_48_1_IntegralClosure
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Construction

/-!
# Integral closure of the target structure sheaf in a direct image

Compatibility names and typed checks for the quasi-coherent pushforward algebra and its
integral-closure algebra.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The direct-image structure morphism of commutative-ring sheaves. -/
abbrev commRingStructureSheafMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingStructureSheaf Y ⟶
      (commRingPushforward f).obj (commRingStructureSheaf X) :=
  commStructureSheafMap f

#check (pushforwardStructureQcAlgebra :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    Y.QcAlgebraUnder)

#check (pushforwardStructureQcAlgebra_forget₂ :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (pushforwardStructureQcAlgebra f).obj.right =
      pushforwardStructureAlgebra f)

#check (pushforwardStructureQcAlgebra_sheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    (pushforwardStructureQcAlgebra f).obj.right =
      (commRingPushforward f).obj (commRingStructureSheaf X))

#check (integralClosureAlgebra :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    Y.QcAlgebraUnder)

#check (integralClosureAlgebra_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    integralClosureAlgebra f =
      QcAlgebraUnder.integralClosure (pushforwardStructureQcAlgebra f))

#check (integralClosureAlgebra_inclusion :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    integralClosureAlgebra f ⟶ pushforwardStructureQcAlgebra f)

#check (integralClosureAlgebra_inclusion_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    integralClosureAlgebra_inclusion f =
      QcAlgebraUnder.inclusion (pushforwardStructureQcAlgebra f))

end AlgebraicGeometry.AlgebraicSpace
