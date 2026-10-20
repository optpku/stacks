/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.AssociatedCycle

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 42.14.4 (1): flat pullback by a morphism of relative dimension `r`
sends a closed subscheme of `δ`-dimension at most `k` to one of dimension at
most `k + r`. -/
@[stacks 02RE] #check
  (AlgebraicGeometry.Scheme.Hom.closedSubschemeDeltaDimension_comap_le :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (Z : Y.left.IdealSheafData) (k : ℤ),
      Y.hom.closedSubschemeDeltaDimension δ Z ≤ (k : EInt) →
        X.hom.closedSubschemeDeltaDimension δ (Z.comap f.left) ≤
          ((k + (r : ℤ) : ℤ) : EInt))

/- Lemma 42.14.4 (2): the degree-`k + r` cycle of the inverse-image closed
subscheme is the flat pullback of its degree-`k` cycle. -/
@[stacks 02RE] #check
  (AlgebraicGeometry.CycleGroup.flatPullback_closedSubschemeCycle :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (Z : Y.left.IdealSheafData) (k : ℤ)
      (hZ : Y.hom.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)),
      X.hom.closedSubschemeCycle δ (Z.comap f.left) (k + (r : ℤ))
          (Scheme.Hom.closedSubschemeDeltaDimension_comap_le δ X Y f r Z k hZ) =
        CycleGroup.flatPullback δ X Y f r k
          (Y.hom.closedSubschemeCycle δ Z k hZ))

/- Lemma 42.14.4 (3): flat pullback by a morphism of relative dimension `r`
sends the support of a coherent module of `δ`-dimension at most `k` to one of
dimension at most `k + r`. -/
@[stacks 02RE] #check
  (AlgebraicGeometry.Scheme.Modules.pullbackSupportDeltaDimension_le :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (F : Y.left.Modules) [F.IsCoherent] (k : ℤ),
      Y.hom.closedSubschemeDeltaDimension δ (Scheme.Modules.schemeTheoreticSupport F) ≤
          (k : EInt) →
        X.hom.closedSubschemeDeltaDimension δ
            (Scheme.Modules.schemeTheoreticSupport ((Scheme.Modules.pullback f.left).obj F)) ≤
          ((k + (r : ℤ) : ℤ) : EInt))

/- Lemma 42.14.4 (4): flat pullback of the degree-`k` cycle associated to a
coherent module is the degree-`k + r` cycle associated to its pulled-back
module. -/
@[stacks 02RE] #check
  (AlgebraicGeometry.Scheme.Modules.associatedCycle_pullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (F : Y.left.Modules) [hcoh : F.IsCoherent] (k : ℤ),
      Y.hom.closedSubschemeDeltaDimension δ (Scheme.Modules.schemeTheoreticSupport F) ≤
          (k : EInt) →
        CycleGroup.flatPullback δ X Y f r k
            (Scheme.Modules.relativeAssociatedCycle Y.hom δ F k) =
          Scheme.Modules.relativeAssociatedCycle
            (hF := @Scheme.Modules.pullback_isCoherent X.left Y.left
              (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (LocallyOfFiniteType.isLocallyNoetherian Y.hom) f.left F hcoh)
            X.hom δ
            ((Scheme.Modules.pullback f.left).obj F) (k + (r : ℤ)))

end AlgebraicGeometry
