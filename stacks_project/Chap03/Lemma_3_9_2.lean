module

public import ReasLib.AlgebraicGeometry.Scheme.VonNeumann
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory
open scoped ZFSet

/- Lemma 3.9.2. Every set of set-presented schemes is contained in a limit level `V_α`
whose full scheme subcategory represents all schemes within the prescribed size bound
and detects countable limits and colimits with isomorphic canonical comparison maps. -/
@[stacks 000J] #check (AlgebraicGeometry.Scheme.exists_isSmallBoundClosed :
  ∀ {ι : Type u} (S0 : ι → AlgebraicGeometry.Scheme.SetPresentation.{u}),
    ∃ α : Ordinal.{u}, Order.IsSuccLimit α ∧
      AlgebraicGeometry.Scheme.IsSmallBoundClosed
        (AlgebraicGeometry.Scheme.vonNeumannStage α) ∧
      (∀ i, (S0 i).code ∈ V_ α) ∧
      ObjectProperty.ofObj (fun i ↦ (S0 i).toScheme) ≤
        AlgebraicGeometry.Scheme.vonNeumannStage α)
