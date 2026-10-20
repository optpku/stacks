module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Qcqs.Projective
public import ReasLib.AlgebraicGeometry.Scheme.Reduction
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Immersion

/-!
# Refinements of qcqs Chow modifications

This file records reduced-source and finite-presentation refinements of qcqs Chow modifications.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ChowLemmaQcqsModification

/-- A separated finite-type morphism to a quasi-compact, quasi-separated scheme admits a qcqs
Chow modification with reduced source. -/
theorem exists_isReduced
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f] :
    ∃ M : ChowLemmaQcqsModification f, IsReduced M.X' := sorry

/-- A separated finite-type morphism to a quasi-compact, quasi-separated scheme admits a qcqs
Chow modification whose morphism to the original scheme is of finite presentation. -/
theorem exists_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f] :
    ∃ M : ChowLemmaQcqsModification f, Scheme.Hom.FinitePresentation M.π := sorry

end AlgebraicGeometry.ChowLemmaQcqsModification
