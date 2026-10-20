/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage

/-!
# Reduced complements of open subspaces

The complement of an open subspace has a canonical reduced induced closed
subspace structure. Its inverse image along a morphism is the corresponding
fibre product, equipped with its canonical projection to the complement.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/-- The reduced induced closed subspace `T = W \ U` on the complement of an open
subspace `U ⊂ W`. -/
def reducedComplement {S : Scheme.{u}} {W : AlgebraicSpace S} (U : OpenSubspace W) :
    ClosedSubspace W :=
  (ClosedSubspaceStructure.reduced U.pointsOpens.compl).subspace

/-- The reduced complement of `U ⊂ W` has point-set `|W| \ |U|`, is reduced in the
étale-local sense, and is a closed subspace of `W`. -/
theorem reducedComplement_spec {S : Scheme.{u}} {W : AlgebraicSpace S}
    (U : OpenSubspace W) :
    U.reducedComplement.pointsSet = U.pointsSetᶜ ∧
      hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
        U.reducedComplement.X ∧
      IsClosedImmersion U.reducedComplement.ι :=
  sorry

/-- The inclusion of the reduced complement of an open subspace is a closed immersion. -/
def reducedComplement_isClosedImmersion {S : Scheme.{u}}
    {W : AlgebraicSpace S} (U : OpenSubspace W) :
    IsClosedImmersion U.reducedComplement.ι :=
  U.reducedComplement.isClosedImmersion

/-- The inverse image `f⁻¹(T)` of the reduced complement `T` of `U ⊂ W`. -/
abbrev preimage {S : Scheme.{u}} {V W : AlgebraicSpace S} (U : OpenSubspace W)
    (f : V ⟶ W) : AlgebraicSpace S :=
  @inverseImage S W V U.reducedComplement.X f U.reducedComplement.ι
    U.reducedComplement_isClosedImmersion

/-- The canonical comparison `f⁻¹(T) ⟶ T` for the reduced complement of `U ⊂ W`. -/
abbrev preimageTo {S : Scheme.{u}} {V W : AlgebraicSpace S} (U : OpenSubspace W)
    (f : V ⟶ W) : U.preimage f ⟶ U.reducedComplement.X :=
  @inverseImageTo S W V U.reducedComplement.X f U.reducedComplement.ι
    U.reducedComplement_isClosedImmersion

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
