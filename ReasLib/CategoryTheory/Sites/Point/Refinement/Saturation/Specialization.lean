module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Separating
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Stage
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.SeparatingDiagram
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Diagram
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Specialization.Initial

/-!
# Specialization Bridges for Saturation Refinements

This umbrella exports the forgetful bridges from separating and scheduled saturation stages to
the neutral refinement-stage and target-diagram APIs, together with canonical initial-stage
constructors.  The tower-level bridge is exported by the broader `Saturation` umbrella because
its construction depends on the saturation limit layer.
-/
