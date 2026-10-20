module

public import ReasLib.Algebra.Module.Graded.Left
public import ReasLib.Algebra.Module.Graded.Action
public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import ReasLib.Algebra.Module.Graded.Span
public import ReasLib.Algebra.Module.Graded.Span.Finite
public import ReasLib.Algebra.Module.Graded.Span.RestrictScalars
public import ReasLib.Algebra.Module.Graded.Quotient
public import ReasLib.Algebra.Module.Graded.Quotient.RestrictScalars
public import ReasLib.Algebra.Module.Graded.Quotient.Finite
public import ReasLib.Algebra.Module.Graded.NatToInt
public import ReasLib.Algebra.Module.Graded.Submodule

/-!
# Core graded-module support

This is the lightweight aggregate for reusable graded-module infrastructure.  It contains the
carrier-level owners for homogeneous maps, homogeneous spans, quotient gradings, restricted-scalar
quotients, and natural-to-integer reindexing.  Category and shift constructions remain in their
dedicated leaves so a basic grading consumer does not import categorical infrastructure.
-/
