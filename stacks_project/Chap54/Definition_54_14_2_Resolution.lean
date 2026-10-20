module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence

open AlgebraicGeometry TopologicalSpace

universe u

/- Finite normalized-blowup sequences retain their initial and terminal schemes. -/
#check (AlgebraicGeometry.Scheme.NormalizedBlowupSequence :
  Scheme.{u} → Scheme.{u} → Type (u + 1))

/- Resolution by normalized blowups is a predicate on two-dimensional Noetherian integral
schemes. -/
#check (AlgebraicGeometry.Scheme.HasResolutionByNormalizedBlowups :
  ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsIntegral Y], topologicalKrullDim Y = 2 → Prop)
