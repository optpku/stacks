module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissage.StandardShrinking
public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAtAmbientPoint.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.StandardShrinking.Existence

/-!
# Existence of standard shrinkings of complete dévissages

This module provides complete standard shrinkings with prescribed control over the
base, terminal model, or source open.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint.StandardShrinking

variable {S X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] {x : X}

/-- Restriction to a prescribed basic-open neighbourhood of the base point gives a
complete standard shrinking whose source and stage opens are the corresponding
inverse images. -/
theorem existsOfBase (D : CompleteDevissageAtAmbientPoint f F x) (S' : S.Opens)
    (a : Γ(S, ⊤)) (h_standard : S' = S.basicOpen a)
    (h_neighbourhood : f x ∈ S') :
    ∃ W : D.StandardShrinking,
      W.base = S' ∧
        W.source = f ⁻¹ᵁ S' ∧
        (∀ k, W.auxiliary k = (D.toCompleteDevissageOver.stage k).Z.hom ⁻¹ᵁ S') ∧
        ∀ k, W.model k = (D.toCompleteDevissageOver.stage k).Y.hom ⁻¹ᵁ S' := sorry

/-- Every basic-open neighbourhood of the distinguished terminal model point becomes
the terminal model open of a complete standard shrinking after restriction over its
base. -/
theorem existsWithTerminalModel (D : CompleteDevissageAtAmbientPoint f F x)
    (V : (D.toCompleteDevissageOver.stage
      (Fin.last D.toCompleteDevissageOver.last)).Y.left.Opens)
    (a : Γ((D.toCompleteDevissageOver.stage
      (Fin.last D.toCompleteDevissageOver.last)).Y.left, ⊤))
    (h_standard : V = (D.toCompleteDevissageOver.stage
      (Fin.last D.toCompleteDevissageOver.last)).Y.left.basicOpen a)
    (h_neighbourhood : D.y (Fin.last D.toCompleteDevissageOver.last) ∈ V) :
    ∃ W : D.StandardShrinking,
      W.model (Fin.last D.toCompleteDevissageOver.last) =
        V ⊓ ((D.toCompleteDevissageOver.stage
          (Fin.last D.toCompleteDevissageOver.last)).Y.hom ⁻¹ᵁ W.base) := sorry

/-- Every open neighbourhood of the distinguished source point contains the source
open of a complete standard shrinking. -/
theorem existsSourceLE (D : CompleteDevissageAtAmbientPoint f F x) (U : X.Opens)
    (h_neighbourhood : x ∈ U) :
    ∃ W : D.StandardShrinking, W.source ≤ U := sorry

end AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint.StandardShrinking
