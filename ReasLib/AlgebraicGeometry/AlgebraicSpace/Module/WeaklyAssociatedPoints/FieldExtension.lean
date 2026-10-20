module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FieldExtension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly associated points under field extension

Weak association of a point to a quasi-coherent module on an algebraic space
descends along the projection from a field-extension base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension

/-- A weakly associated point of the field-extension pullback of a quasi-coherent
module maps to a weakly associated point of the original module. -/
@[stacks 0CUS]
theorem mem_weakAss_of_mem_weakAss
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules)
    [F.IsQuasicoherent]
    (y : Points (GenericFiber.baseChange k K X))
    (hy : y ∈ (baseChange k K F).weakAss) :
    Points.map (GenericFiber.toSource k K X) y ∈ F.weakAss :=
  sorry

/-- The image of the weakly associated locus of a field-extension pullback is
contained in the weakly associated locus of the original quasi-coherent module. -/
theorem weakAss_map_subset
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules)
    [F.IsQuasicoherent] :
    Points.map (GenericFiber.toSource k K X) ''
        (baseChange k K F).weakAss ⊆ F.weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension
