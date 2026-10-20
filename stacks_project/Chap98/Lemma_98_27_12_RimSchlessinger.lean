module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.RimSchlessinger

/-! Compatibility checks for locally Noetherian embeddings and the RS condition. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

#check (AlgebraicGeometry.Scheme.Over.asLocallyNoetherian :
  ∀ {S : Scheme.{u}} (X : Over S) [IsLocallyNoetherian X.left],
    (AlgebraicGeometry.Scheme.Over.locallyNoetherian S).FullSubcategory)

#check (AlgebraicGeometry.Scheme.Over.HasRimSchlessinger :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S],
    ((AlgebraicGeometry.Scheme.Over.locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v) → Prop)
