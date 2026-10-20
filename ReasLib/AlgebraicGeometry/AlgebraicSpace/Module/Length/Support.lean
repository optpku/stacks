module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Topology.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Finite nonzero length and generic points of coherent support
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]

/-- For a coherent module on a locally Noetherian algebraic space, being a generic point of
an irreducible component of the support on some étale scheme chart, having that property on
every such chart, and having finite nonzero length at the point are equivalent. -/
theorem hasFiniteNonzeroLengthAt_tfae (F : X.Modules) [F.IsCoherent] (x : Points X) :
    List.TFAE
      [∃ (U : Over S) (φ : ofOver U ⟶ X),
          Etale φ ∧ ∃ u : U.left,
            Points.mapOfOver φ u = x ∧
              IsGenericPoint.ofIrreducibleComponent u
                (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
          Points.mapOfOver φ u = x →
            IsGenericPoint.ofIrreducibleComponent u
              (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        hasFiniteNonzeroLengthAt F x] :=
  sorry

/-- For a coherent module on a locally Noetherian decent algebraic space, the chartwise
component-generic-point conditions and finite nonzero length at a point are also equivalent
to being a generic point of an irreducible component of the global support. -/
theorem hasFiniteNonzeroLengthAt_tfae_of_isDecent [IsDecent X] (F : X.Modules) [F.IsCoherent]
    (x : Points X) :
    List.TFAE
      [∃ (U : Over S) (φ : ofOver U ⟶ X),
          Etale φ ∧ ∃ u : U.left,
            Points.mapOfOver φ u = x ∧
              IsGenericPoint.ofIrreducibleComponent u
                (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
          Points.mapOfOver φ u = x →
            IsGenericPoint.ofIrreducibleComponent u
              (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        hasFiniteNonzeroLengthAt F x,
        IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
