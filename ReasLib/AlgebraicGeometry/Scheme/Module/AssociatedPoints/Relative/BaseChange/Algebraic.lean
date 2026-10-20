module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Extension
public import ReasLib.RingTheory.KrullDimension.Integral.Zero

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.relativeAssassin

/-- Under arbitrary base change, the relative assassin of a pulled-back quasicoherent module
is contained in the inverse image of the original relative assassin. -/
theorem pullback_subset_preimage
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    relativeAssassin f' ((Scheme.Modules.pullback g').obj ℱ) ⊆
      g' ⁻¹' relativeAssassin f ℱ := sorry

/-- Under base change with algebraic residue-field extensions, the inverse image of the
relative assassin equals the relative assassin of the pulled-back quasicoherent module. -/
theorem preimage_eq_pullback_of_algebraicResidueFieldExtensions
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (hg : Scheme.Hom.HasAlgebraicResidueFieldExtensions g)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    g' ⁻¹' relativeAssassin f ℱ =
      relativeAssassin f' ((Scheme.Modules.pullback g').obj ℱ) := sorry

/-- Under locally quasi-finite base change, the inverse image of the relative assassin equals
the relative assassin of the pulled-back quasicoherent module. -/
theorem preimage_eq_pullback_of_locallyQuasiFinite
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [LocallyOfFiniteType f]
    [LocallyQuasiFinite g] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    g' ⁻¹' relativeAssassin f ℱ =
      relativeAssassin f' ((Scheme.Modules.pullback g').obj ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.relativeAssassin
