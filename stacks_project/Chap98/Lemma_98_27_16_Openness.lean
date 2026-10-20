module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.OpennessOfVersality

/-! Compatibility check for openness of versality of Type-valued functors. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u v

#check (AlgebraicGeometry.Scheme.Over.OpennessOfVersality :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    (F : (AlgebraicGeometry.Scheme.Over.locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v),
    Prop)
