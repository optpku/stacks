module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Factorization

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.QuasiFinite

/-- A separated quasi-finite morphism of finite presentation to a quasi-compact
quasi-separated scheme factors as a quasi-compact open immersion followed by a finite morphism
of finite presentation. -/
theorem exists_openImmersion_finitePresentationFactorization
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiFinite f] [IsSeparated f]
    [LocallyOfFinitePresentation f] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (π : T ⟶ S),
      QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧
        Scheme.Hom.FinitePresentation π ∧ j ≫ π = f := sorry

end AlgebraicGeometry.Scheme.Hom.QuasiFinite
