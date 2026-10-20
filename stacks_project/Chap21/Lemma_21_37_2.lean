/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LowerShriek
import StacksCheckRecall

@[expose] public section

-- Local instance justification (defeq pin): the explicit single-complex checks use the standard
-- derived-category quotient underlying the ringed-site ModuleDerived presentation.
attribute [local instance] HasDerivedCategory.standard

open CategoryTheory RingedSite.Cocontinuous
open SheafOfModules.Localization

noncomputable section

universe z uC vC uD vD w

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{w})

/-!
# Lemma 21.37.2

The Stacks existence statements remain unconditional. The functor, adjunction, and generator
isomorphism consume the corresponding supplied certificates while their proofs remain pending.
-/

section Existence

variable [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}]

/- Lemma 21.37.2 (07AC) (1): existence of the total left-derived lower shriek. -/
@[stacks 07AC "(1) derived lower-shriek existence"]
#check (moduleLowerShriek.toDerived.hasLeftDerived (J := J) (K := K) f R :
  Functor.HasLeftDerivedFunctor (moduleLowerShriek.toDerived (J := J) (K := K) f R)
    (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.source (J := J) (K := K) f R)))

variable [Functor.HasLeftDerivedFunctor
  (moduleLowerShriek.toDerived (J := J) (K := K) f R)
  (RingedSite.Hom.ModuleQis.{z} (moduleInverseImage.source (J := J) (K := K) f R))]

/- Lemma 21.37.2 (07AC) (2): the absolute-derived adjunction certificate exists. -/
@[stacks 07AC "(2) absolute-derived adjunction certificate"]
#check (moduleLowerShriek.derived.hasPair (J := J) (K := K) f R :
  moduleLowerShriek.derived.HasPair (J := J) (K := K) f R)

variable [moduleLowerShriek.derived.HasPair (J := J) (K := K) f R]

/- Lemma 21.37.2 (07AC) (2): the derived adjunction for the supplied certificate. -/
@[stacks 07AC "(2) exact-derived adjunction"]
#check (moduleLowerShriek.derived.adjunction (J := J) (K := K) f R :
  moduleLowerShriek.derived (J := J) (K := K) f R ⊣
    moduleInverseImage.derived (J := J) (K := K) f R)

end Existence

section Generator

variable (U : C)
variable [HasLowerShriek.{w} (inverseImageRingSheaf (J := J) (K := K) f R)]
variable [HasLowerShriek.{w} R]
variable [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}]

/- Lemma 21.37.2 (07AC) (3): the localized structure module computes the derived value. -/
@[stacks 07AC "(3) generator computes derived lower shriek"]
#check (moduleLowerShriek.derived.structureModuleComputesAt f R U :
  Functor.LeftDerived.ComputesAt (moduleLowerShriek.toDerived (J := J) (K := K) f R)
    (RingedSite.Hom.ModuleQis.{w} (moduleInverseImage.source (J := J) (K := K) f R))
    (moduleLowerShriek.derived.structureModuleHomotopy f R U))

variable [Functor.HasPointwiseLeftDerivedFunctor
  (moduleLowerShriek.toDerived (J := J) (K := K) f R)
  (RingedSite.Hom.ModuleQis.{w} (moduleInverseImage.source (J := J) (K := K) f R))]
variable (h_compute : Functor.LeftDerived.ComputesAt
  (moduleLowerShriek.toDerived (J := J) (K := K) f R)
  (RingedSite.Hom.ModuleQis.{w} (moduleInverseImage.source (J := J) (K := K) f R))
  (moduleLowerShriek.derived.structureModuleHomotopy f R U))

/- Lemma 21.37.2 (07AC) (3): the derived generator calculation for the supplied computation. -/
@[stacks 07AC "(3) derived generator isomorphism"]
#check (moduleLowerShriek.derived.structureModuleIso f R U h_compute :
  (moduleLowerShriek.derived (J := J) (K := K) f R).obj
    ((DerivedCategory.singleFunctor
      (RingedSite.ModuleCat.{w} (moduleInverseImage.source (J := J) (K := K) f R)) 0).obj
      (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U)) ≅
    (DerivedCategory.singleFunctor
      (RingedSite.ModuleCat.{w} (moduleInverseImage.target (K := K) R)) 0).obj
      (structureModule R (f.obj U)))

end Generator
