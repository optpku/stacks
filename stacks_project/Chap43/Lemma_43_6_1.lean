/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Pushforward
import ReasLib.AlgebraicGeometry.Scheme.OverField
import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
import ReasLib.AlgebraicGeometry.Scheme.Variety
import ReasLib.RingTheory.Catenary.Field
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

section

variable {K : Type u} [Field K]
variable (X Y : SchemeOverField K) [Variety X] [Variety Y]
variable (f : X ⟶ Y) [IsProper f.left]

section

variable (F : X.left.Modules) [F.IsCoherent] (k : ℤ)
variable (hF : X.hom.closedSubschemeDeltaDimension
  (fun _ : Spec (CommRingCat.of K) ↦ 0) (Scheme.Modules.schemeTheoreticSupport F) ≤
    (k : EInt))

/- Lemma 43.6.1 (1): for a proper morphism of varieties, proper pushforward of the
degree-`k` associated cycle of a coherent sheaf agrees with the degree-`k` associated
cycle of its pushforward. -/
@[stacks 0AZD] #check
  (AlgebraicGeometry.Scheme.Modules.map_associatedCycle_eq_pushforward_associatedCycle
      (fun _ : Spec (CommRingCat.of K) ↦ 0) X Y f F k hF :
    AlgebraicCycle.map f.left
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (@Scheme.Modules.associatedCycle X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom) F inferInstance
          (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)) k) =
      @Scheme.Modules.associatedCycle Y.left
        (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        ((Scheme.Modules.pushforward f.left).obj F)
        (@Scheme.Modules.pushforward_obj_isCoherent_of_proper X.left Y.left f.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom) inferInstance F inferInstance)
        (Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)) k)

end

section

variable (Z : X.left.IdealSheafData) (k : ℤ)
variable (hZ : X.hom.closedSubschemeDeltaDimension
  (fun _ : Spec (CommRingCat.of K) ↦ 0) Z ≤ (k : EInt))

/- Lemma 43.6.1 (2): for a proper morphism of varieties, proper pushforward of the
degree-`k` cycle of a closed subscheme agrees with the degree-`k` associated cycle of
the pushforward of its structure sheaf. -/
@[stacks 0AZD] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.map_cycle_eq_pushforward_associatedCycle
      (fun _ : Spec (CommRingCat.of K) ↦ 0) X Y f Z k hZ :
    AlgebraicCycle.map f.left
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (X.hom.closedSubschemeCycle
          (fun _ : Spec (CommRingCat.of K) ↦ 0) Z k hZ : AlgebraicCycle X.left ℤ) =
      @Scheme.Modules.associatedCycle Y.left
        (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        ((Scheme.Modules.pushforward f.left).obj (closedSubschemeStructureSheafOn Z))
        (@Scheme.Modules.pushforward_obj_isCoherent_of_proper X.left Y.left f.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom) inferInstance
          (closedSubschemeStructureSheafOn Z)
          (@Scheme.Modules.pushforward_obj_isCoherent_of_isFinite Z.subscheme X.left
            Z.subschemeι inferInstance (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (SheafOfModules.unit Z.subscheme.ringCatSheaf)
            (@Scheme.Modules.structureSheaf_isCoherent Z.subscheme
              (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X.left
                (LocallyOfFiniteType.isLocallyNoetherian X.hom) Z))))
        (Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)) k)

end


end
