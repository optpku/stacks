module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.InfinitesimalNeighbourhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing

/-!
# Conormal comparison for first-order infinitesimal neighbourhoods

The identity square relating an immersion of algebraic spaces to its first-order
infinitesimal neighbourhood induces a canonical isomorphism of conormal sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom.InfinitesimalNeighbourhood

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

/-- The identity square relating an immersion `i : Z ⟶ X` to the closed immersion
from `Z` into its first-order infinitesimal neighbourhood `space i 1`. -/
theorem firstOrderConormalSq (i : Z ⟶ X) [IsImmersion i] :
    CommSq (𝟙 Z) (fromSource i 1) i (toAmbient i 1) :=
  sorry

/-- The canonical comparison `Hom.conormalSheaf i ⟶ Hom.conormalSheaf (fromSource i 1)`
obtained from `Hom.Conormal.map` of `firstOrderConormalSq i`, after transporting
along `SmallEtaleModuleGlueing.modulesPullbackId`. -/
noncomputable def conormalComparison (i : Z ⟶ X) [IsImmersion i] :
    Hom.conormalSheaf i ⟶ Hom.conormalSheaf (fromSource i 1) :=
  (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (Hom.conormalSheaf i) ≫
    Hom.Conormal.map (firstOrderConormalSq i)

/-- `conormalComparison` is the identity-pullback correction of
`Hom.Conormal.map (firstOrderConormalSq i)`. -/
theorem conormalComparison_eq (i : Z ⟶ X) [IsImmersion i] :
    conormalComparison i =
      (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (Hom.conormalSheaf i) ≫
        Hom.Conormal.map (firstOrderConormalSq i) :=
  sorry

/-- The canonical comparison from the conormal sheaf of an immersion to the
conormal sheaf of its first-order infinitesimal neighbourhood is an isomorphism. -/
instance conormalComparison_isIso {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] :
    IsIso (conormalComparison i) :=
  sorry

end Hom.InfinitesimalNeighbourhood

end AlgebraicGeometry.AlgebraicSpace
