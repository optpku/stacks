module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DerivedRestriction

/-!
# Compatibility surface for derived restriction
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {Y X : Scheme.{u}} {Λ : Type w} [Ring Λ]
variable [Abelian (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [Abelian (Sheaf (topology Y) (ModuleCat.{w} Λ))]
variable [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ))]

/- The shared derived restriction functor is available under the established API. -/
#check (restrictDerived (X := X) (Y := Y) (Λ := Λ) :
  ∀ (f : Y ⟶ X)
    [∀ P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ, (baseChange f).op.HasLeftKanExtension P]
    [HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
    [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
    [HasDerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ))],
    DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ)) ⥤
      DerivedCategory (Sheaf (topology Y) (ModuleCat.{w} Λ)))

end AlgebraicGeometry.Scheme.ProEt
