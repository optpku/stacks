module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing

@[expose] public section

universe u

namespace CategoryTheory.DerivedCategory

/-- A Noetherian commutative ring admits a canonical dualizing complex if some monoidal
presentation identifies canonical module `RHom` and its regular degree-zero unit with a
closed presentation in which a complex satisfies the canonical dualizing conditions. -/
def HasCanonicalDualizingComplex (A : Type u) [CommRing A] [IsNoetherianRing A] : Prop :=
  ∃ (presentation : MonoidalCategory (DerivedCategory (ModuleCat.{u} A)))
    (C : @CanonicalClosedPresentation A _ presentation)
    (K : DerivedCategory (ModuleCat.{u} A)),
    @IsCanonicalDualizingComplex A _ _ presentation K C

/-- Existence of a canonical dualizing complex is equivalent to existence of a canonical
closed presentation and a complex satisfying its dualizing conditions. -/
theorem hasCanonicalDualizingComplex_iff
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    HasCanonicalDualizingComplex A ↔
      ∃ (presentation : MonoidalCategory (DerivedCategory (ModuleCat.{u} A)))
        (C : @CanonicalClosedPresentation A _ presentation)
        (K : DerivedCategory (ModuleCat.{u} A)),
        @IsCanonicalDualizingComplex A _ _ presentation K C :=
  Iff.rfl

end CategoryTheory.DerivedCategory
