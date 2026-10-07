module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Affine
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.BaseChange

/-!
# Representability of fixed-degree relative projective functors

The functor associated to fixed-degree relative projective quadruples is representable over an
arbitrary base scheme.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor

/-- A fixed-degree relative projective functor associated to quadruples is representable by a
scheme. -/
theorem isRepresentable
    {S : Scheme.{u}} {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf} {d : ℕ}
    [𝒜.IsCommutative]
    (F_d : Scheme.RelativeProjDegreeFunctor S 𝒜 d)
    (associatedToQuadruples : F_d.IsAssociatedToQuadruples) :
    F_d.toFunctor.IsRepresentable := sorry

end AlgebraicGeometry.Scheme.RelativeProjDegreeFunctor
