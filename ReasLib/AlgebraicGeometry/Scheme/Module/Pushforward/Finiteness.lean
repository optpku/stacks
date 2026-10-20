module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.Serre
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a universally catenary locally Noetherian scheme, the boundary depth and
point-closure dimension criterion is equivalent to coherence of low-degree higher direct images.
-/
theorem depth_add_pointClosureDim_gt_iff_higherDirectImage_isCoherent
    {X : Scheme.{u}} [UniversallyCatenary X] (U : X.Opens)
    (F : U.toScheme.Modules) [F.IsCoherent] (n : ℕ)
    (h_formal : ∀ z : X, z ∉ U →
      (FieldAlgebraProperty.serreConditionS n).HoldsOnFormalFibers
        (X.presheaf.stalk z)) :
    (∀ x : U, x ∈ RingedSpace.moduleSupport F →
      ∀ y : PointClosure.scheme (U.ι x),
        PointClosure.ι (U.ι x) y ∉ U →
          (.some (n : ℕ∞) : WithBot ℕ∞) <
            (.some (moduleDepth ((U : Scheme).presheaf.stalk x)
              (RingedSpace.stalkModuleCat F x)) : WithBot ℕ∞) +
                ringKrullDim
                  ((PointClosure.scheme (U.ι x)).presheaf.stalk y)) ↔
      ∀ p : ℕ, p < n →
        (RingedSpace.Hom.higherDirectImageModule U.ι.toShHom F p).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
