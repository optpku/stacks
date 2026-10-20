module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.StructureSheafCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
import Mathlib.Tactic.CrossRefAttribute

/-!
# Proper pushforward of associated cycles

This file compares proper pushforward of cycles with the associated cycles of ordinary
pushforwards of coherent modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Proper pushforward commutes with taking the degree-`k` associated cycle of a coherent
module whose scheme-theoretic support has relative dimension at most `k`. -/
@[stacks 02R6]
theorem map_associatedCycle_eq_pushforward_associatedCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (F : X.left.Modules) [F.IsCoherent] (k : ℤ)
    (hF : X.hom.closedSubschemeDeltaDimension delta (schemeTheoreticSupport F) ≤
      (k : EInt)) :
    AlgebraicCycle.map f.left (X.hom.relativeDimensionFunction delta)
        (Y.hom.relativeDimensionFunction delta)
        (@associatedCycle X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          F inferInstance (X.hom.relativeDimensionFunction delta) k) =
      @associatedCycle Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        ((Scheme.Modules.pushforward f.left).obj F)
        (@pushforward_obj_isCoherent_of_proper X.left Y.left f.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom) inferInstance F inferInstance)
        (Y.hom.relativeDimensionFunction delta) k := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Proper pushforward of the degree-`k` cycle of a closed subscheme agrees with the
degree-`k` associated cycle of the pushforward of its structure sheaf. -/
@[stacks 02R6]
theorem map_cycle_eq_pushforward_associatedCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (Z : X.left.IdealSheafData) (k : ℤ)
    (hZ : X.hom.closedSubschemeDeltaDimension delta Z ≤ (k : EInt)) :
    AlgebraicCycle.map f.left (X.hom.relativeDimensionFunction delta)
        (Y.hom.relativeDimensionFunction delta)
        (X.hom.closedSubschemeCycle delta Z k hZ : AlgebraicCycle X.left ℤ) =
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
              (@subschemeIsLocallyNoetherian X.left
                (LocallyOfFiniteType.isLocallyNoetherian X.hom) Z))))
        (Y.hom.relativeDimensionFunction delta) k := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
