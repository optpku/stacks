module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Functoriality.Identity.Components
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Functoriality.Composition.Components

/-!
# Component computations for universal diagram-map functoriality

This compatibility aggregate exposes the vertexwise identity and composition coherence formulas
for universal maps induced by diagram transformations. The identity and composition owners remain
separate, while downstream clients can import this one focused path when both component APIs are
needed.
-/
