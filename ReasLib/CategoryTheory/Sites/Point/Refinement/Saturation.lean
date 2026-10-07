module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Target
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.TargetDiagram
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Refinement
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementDiagram
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementAdvance
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.RefinementTower
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Stage
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Diagram
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Advance
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Limit
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.OpenTower
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Tower
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Tower

/-!
# Saturation refinements

This is the narrow stable import for the reusable saturation API.  It exports
source-free targets and target diagrams, source-refinement bridges, their
unseparated advance and tower, based scheduled diagrams, and the
separation-specialized advance/tower without importing any Chapter 7
presentation.

Use `Target` and `Target.Diagram` whenever an argument only needs compatible
target refinements and finite-cover lifting.  Use `RefinementStage` when a
construction also records its factorization from a fixed original system, and
use `Stage` only when it must additionally retain chosen separation or
scheduling data.
-/

@[expose] public section

open CategoryTheory
open GrothendieckTopology.Point.ofIsCofiltered

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

/-! Canonical recall surface for downstream saturation constructions. -/

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
