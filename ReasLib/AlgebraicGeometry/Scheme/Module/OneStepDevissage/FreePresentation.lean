module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage

/-!
# Finite free presentations in one-step dévissages

This module provides finite free maps that are isomorphisms on a generic fibre
and the resulting strict decrease in fibrewise support dimension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace OneStepDevissage

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}

/-- At a generic point of the model fibre, the pushforward of the auxiliary
module admits a finite free map of positive rank whose induced fibre map is
bijective. -/
theorem existsFreeMapFiberBijective (D : OneStepDevissage X F s)
    (ξ : Scheme.Hom.fiber D.Y.hom s)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Scheme.Hom.fiber D.Y.hom s))) :
    ∃ (r : ℕ) (hr : 0 < r)
      (α : (SheafOfModules.freeFin r : Scheme.Modules D.Y.left) ⟶
        (Scheme.Modules.pushforward D.π.left).obj D.G),
      Function.Bijective
        (Scheme.Modules.fiberMap
          ((Scheme.Modules.pullback (Scheme.Hom.fiberι D.Y.hom s)).map α) ξ) := sorry

/-- The fibrewise support dimension of the cokernel of a positive-rank finite
free map that is bijective at a generic fibre point is strictly smaller than
the fibrewise support dimension of the original module. -/
theorem cokernelFiberSupportDimensionLt (D : OneStepDevissage X F s)
    (ξ : Scheme.Hom.fiber D.Y.hom s)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Scheme.Hom.fiber D.Y.hom s)))
    (r : ℕ) (hr : 0 < r)
    (α : (SheafOfModules.freeFin r : Scheme.Modules D.Y.left) ⟶
      (Scheme.Modules.pushforward D.π.left).obj D.G)
    (hα : Function.Bijective
      (Scheme.Modules.fiberMap
        ((Scheme.Modules.pullback (Scheme.Hom.fiberι D.Y.hom s)).map α) ξ)) :
    fiberSupportDimension D.Y.hom (cokernel α) s <
      fiberSupportDimension X.hom F s := sorry

end OneStepDevissage
end AlgebraicGeometry.Scheme.Modules
