/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Pushforward
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 42.12.4 (1): proper pushforward of the degree-`k` cycle of a closed subscheme
agrees with the degree-`k` cycle associated to the pushforward of its structure sheaf. -/
@[stacks 02R6] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.map_cycle_eq_pushforward_associatedCycle :
    {S : Scheme.{u}} → [UniversallyCatenary S] →
      (delta : S → ℤ) → [IsDimensionFunction delta] →
        (X Y : Over S) → [LocallyOfFiniteType X.hom] → [LocallyOfFiniteType Y.hom] →
          (f : X ⟶ Y) → [IsProper f.left] →
            (Z : X.left.IdealSheafData) → (k : ℤ) →
              (hZ : X.hom.closedSubschemeDeltaDimension delta Z ≤ (k : EInt)) →
                AlgebraicCycle.map f.left (X.hom.relativeDimensionFunction delta)
                    (Y.hom.relativeDimensionFunction delta)
                    (X.hom.closedSubschemeCycle delta Z k hZ : AlgebraicCycle X.left ℤ) =
                  @Scheme.Modules.associatedCycle Y.left
                    (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
                    ((Scheme.Modules.pushforward f.left).obj
                      (closedSubschemeStructureSheafOn Z))
                    (@Scheme.Modules.pushforward_obj_isCoherent_of_proper X.left Y.left f.left
                      (LocallyOfFiniteType.isLocallyNoetherian Y.hom) inferInstance
                      (closedSubschemeStructureSheafOn Z)
                      (@Scheme.Modules.pushforward_obj_isCoherent_of_isFinite Z.subscheme X.left
                        Z.subschemeι inferInstance
                        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                        (SheafOfModules.unit Z.subscheme.ringCatSheaf)
                        (@Scheme.Modules.structureSheaf_isCoherent Z.subscheme
                          (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X.left
                            (LocallyOfFiniteType.isLocallyNoetherian X.hom) Z))))
                    (Y.hom.relativeDimensionFunction delta) k)

/- Lemma 42.12.4 (2): proper pushforward of the degree-`k` associated cycle of a coherent
module agrees with the degree-`k` associated cycle of its ordinary pushforward. -/
@[stacks 02R6] #check
  (AlgebraicGeometry.Scheme.Modules.map_associatedCycle_eq_pushforward_associatedCycle :
    {S : Scheme.{u}} → [UniversallyCatenary S] →
      (delta : S → ℤ) → [IsDimensionFunction delta] →
        (X Y : Over S) → [LocallyOfFiniteType X.hom] → [LocallyOfFiniteType Y.hom] →
          (f : X ⟶ Y) → [IsProper f.left] →
            (F : X.left.Modules) → [F.IsCoherent] → (k : ℤ) →
              (hF : X.hom.closedSubschemeDeltaDimension delta
                (Scheme.Modules.schemeTheoreticSupport F) ≤ (k : EInt)) →
                AlgebraicCycle.map f.left (X.hom.relativeDimensionFunction delta)
                    (Y.hom.relativeDimensionFunction delta)
                    (@Scheme.Modules.associatedCycle X.left
                      (LocallyOfFiniteType.isLocallyNoetherian X.hom) F inferInstance
                      (X.hom.relativeDimensionFunction delta) k) =
                  @Scheme.Modules.associatedCycle Y.left
                    (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
                    ((Scheme.Modules.pushforward f.left).obj F)
                    (@Scheme.Modules.pushforward_obj_isCoherent_of_proper X.left Y.left f.left
                      (LocallyOfFiniteType.isLocallyNoetherian Y.hom) inferInstance F inferInstance)
                    (Y.hom.relativeDimensionFunction delta) k)
