/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Colimit
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Existence
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Essential
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Flat
public import ReasLib.RingTheory.DirectLimit.FlatModel
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.FiniteType.Finiteness
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Local
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Limit
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Existence
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Finiteness
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Pushout
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.Colimit
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.Properties
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Colimit
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Properties
public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation.CompleteIntersection
public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation.Isomorphism
public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation.Smooth
public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation.Syntomic
public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FiniteType
public import ReasLib.RingTheory.DirectLimit.Algebra.Constant
public import ReasLib.RingTheory.DirectLimit.Algebra.FormallyEtale
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.CompleteIntersection
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.Isomorphism
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.Smooth
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.BaseChange.FinitePresentation.Syntomic
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.BaseChange.FiniteType
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.CommAlg
public import ReasLib.RingTheory.DirectLimit.Algebra.Tail.Tensor
public import ReasLib.RingTheory.Henselian.DirectLimit

/-!
# Ring direct limits

Aggregate import for the reusable ring direct-limit library.  Consumers that
only need system-level infrastructure should import
`ReasLib.RingTheory.DirectLimit.Core`; application-specific consumers may
instead import the corresponding leaf below `DirectLimit.Algebra`.
-/

@[expose] public section
