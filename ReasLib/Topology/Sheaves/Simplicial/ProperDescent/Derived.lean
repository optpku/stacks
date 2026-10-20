module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Derived
public import ReasLib.Topology.Category.LCCat.Simplicial
public import ReasLib.Topology.Category.LCCat.ProperHypercovering

/-!
# Bounded-below cohomological descent for proper hypercoverings

The canonical derived unit of a proper hypercovering of Hausdorff locally compact
spaces is an isomorphism on bounded-below derived categories of abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)
variable [HasSheafify (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X.obj)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}]
variable [(augmentationPushforward (toTopCatAugmentation a)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}))]

/-- For a proper hypercovering of a Hausdorff locally compact space, the canonical
bounded-below derived augmentation unit is an isomorphism at every abelian sheaf complex. -/
theorem plusDerivedUnit_app_isIso (ha : IsProperHypercovering a)
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})) :
    IsIso ((plusDerivedUnit (toTopCatAugmentation a)).app K) :=
  sorry

/-- The derived unit `𝟭 ⟶ a⁻¹ ⋙ Ra_*` is an isomorphism of functors on `D⁺(X)`. -/
theorem plusDerivedUnit_isIso (ha : IsProperHypercovering a) :
    IsIso (plusDerivedUnit (toTopCatAugmentation a)) :=
  (NatTrans.isIso_iff_isIso_app _).2 (fun K => plusDerivedUnit_app_isIso a ha K)

end LCCat

end
