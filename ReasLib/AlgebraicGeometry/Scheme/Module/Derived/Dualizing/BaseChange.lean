module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Scheme.DerivedQCoh

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- For a surjective morphism of locally Noetherian schemes satisfying one of the
syntomic, flat local-complete-intersection, or finite-type Gorenstein conditions,
a quasi-coherent complex is dualizing exactly when its derived pullback is dualizing. -/
theorem iff_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Surjective f]
    (hf : Syntomic f ∨
      (Flat f ∧ LocallyOfType RingHom.IsLocalCompleteIntersection f) ∨
      (AlgebraicGeometry.Gorenstein f ∧ Scheme.Hom.FiniteType f))
    (K : Scheme.DerivedQCoh Y) :
    IsDualizingComplex K.obj ↔
      IsDualizingComplex
        ((Scheme.DerivedQCoh.pullback f).obj K).obj := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
