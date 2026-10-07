module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.Proper

/-!
# Separatedness and properness from DVR-valuative criteria along a dense morphism

This file records refined separatedness and properness criteria in which the generic arrows of
DVR-valuative squares are required to factor through a fixed dense finite-type morphism.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ValuativeCriterion.DVR.Along

/-- Let `f : X ⟶ S` and `h : U ⟶ X` be finite-type morphisms of schemes, with `S` locally
Noetherian, `f` separated, and `h` having dense range. If every DVR-valuative square over `f`
whose generic arrow factors through `h` admits a lift, then `f` is proper. -/
theorem isProper_of_isSeparated {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [IsLocallyNoetherian S] [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType h]
    [IsSeparated f] (h_dense : DenseRange h) (h_valuative : Existence h f) :
    IsProper f := sorry

/-- Let `f : X ⟶ S` be locally of finite type over a locally Noetherian scheme, and let
`h : U ⟶ X` be a finite-type morphism with dense range. If lifts in every DVR-valuative square
over `f` whose generic arrow factors through `h` are unique, then `f` is separated. -/
theorem isSeparated {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [Scheme.Hom.FiniteType h]
    (h_dense : DenseRange h) (h_valuative : Uniqueness h f) :
    IsSeparated f := sorry

/-- Let `f : X ⟶ S` and `h : U ⟶ X` be finite-type morphisms of schemes, with `S` locally
Noetherian and `h` having dense range. If every DVR-valuative square over `f` whose generic
arrow factors through `h` admits a unique lift, then `f` is proper. -/
theorem isProper {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [IsLocallyNoetherian S] [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType h]
    (h_dense : DenseRange h) (h_valuative : ExistsUnique h f) :
    IsProper f := sorry

end AlgebraicGeometry.ValuativeCriterion.DVR.Along
