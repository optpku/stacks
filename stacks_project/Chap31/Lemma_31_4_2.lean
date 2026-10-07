module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints.GenericPoints
import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Support
import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints.Support

open AlgebraicGeometry

universe u

section Module

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/- Lemma 31.4.2 (1): the points minimal under specialization in the support of a coherent module
on a locally Noetherian scheme are associated points of the module. -/
@[stacks 05AL] #check
  (AlgebraicGeometry.Scheme.Modules.minimalSpecializationPoints_support_subset_associatedPoints
      (X := X) ℱ :
    X.minimalSpecializationPoints (AlgebraicGeometry.RingedSpace.moduleSupport ℱ) ⊆
      AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ)

/- Lemma 31.4.2 (2): an associated point of a coherent module on a locally Noetherian scheme is
embedded exactly when it is not minimal under specialization in the support of the module. -/
@[stacks 05AL] #check
  (AlgebraicGeometry.Scheme.Modules.embeddedAssociatedAt.iff_mem_associatedPoints_and_not_minimal
      (X := X) ℱ :
    ∀ x : X,
      ℱ.embeddedAssociatedAt x ↔
        x ∈ AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ ∧
          x ∉ X.minimalSpecializationPoints (AlgebraicGeometry.RingedSpace.moduleSupport ℱ))

end Module

section Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/- Lemma 31.4.2 (3): an embedded point of a locally Noetherian scheme is an associated point
that is not a generic point of an irreducible component. -/
@[stacks 05AL] #check
  (AlgebraicGeometry.Scheme.embeddedPoint_iff_mem_associatedPoints_and_not_mem_genericPoints
      (X := X) :
    ∀ x : X,
      X.embeddedPoint x ↔
        x ∈ X.associatedPoints ∧ x ∉ genericPoints X)

end Scheme
