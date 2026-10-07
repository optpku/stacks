module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import Mathlib.Data.List.TFAE
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.SchemeTheoreticImage

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeTheoreticClosure

variable {X : Scheme.{u}} [IsReduced X]

/-- An open subscheme of a reduced scheme is topologically dense exactly when its
scheme-theoretic closure is the whole scheme. -/
theorem dense_iff_eq_self_of_isReduced (U : X.Opens) :
    Dense (U : Set X) ↔ schemeTheoreticClosure U = X := sorry

/-- An open subscheme of a reduced scheme is topologically dense exactly when it is
scheme-theoretically dense. -/
theorem dense_iff_schemeTheoreticallyDense_of_isReduced (U : X.Opens) :
    Dense (U : Set X) ↔ schemeTheoreticallyDense U := sorry

/-- For an open subscheme of a reduced scheme, topological density, equality of its
scheme-theoretic closure with the whole scheme, and scheme-theoretic density are equivalent. -/
theorem density_tfae_of_isReduced (U : X.Opens) :
    List.TFAE [Dense (U : Set X), schemeTheoreticClosure U = X, schemeTheoreticallyDense U] := sorry

end AlgebraicGeometry.SchemeTheoreticClosure

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (U : X.Opens)

/-- A scheme containing a reduced open subscheme whose scheme-theoretic closure is the
whole scheme is reduced. -/
theorem isReduced_of_schemeTheoreticClosure_eq_self_of_isReduced
    [IsReduced U.toScheme] (hclosure : schemeTheoreticClosure U = X) :
    IsReduced X := sorry

/-- A reduced open subscheme has scheme-theoretic closure equal to the ambient scheme
exactly when it is scheme-theoretically dense. -/
theorem schemeTheoreticClosure_eq_self_iff_schemeTheoreticallyDense_of_isReduced
    [IsReduced U.toScheme] :
    schemeTheoreticClosure U = X ↔ schemeTheoreticallyDense U := sorry

end AlgebraicGeometry
