module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_21_1

/-!
# Rig-surjectivity of monomorphisms of formal algebraic spaces

A locally of finite type monomorphism of locally Noetherian formal algebraic
spaces is rig-surjective if and only if every adic test map from the formal
spectrum of a complete discrete valuation ring factors through the source,
with no extension of discrete valuation rings required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- Lemma 88.21.11: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces. Assume `X` and `Y` are locally Noetherian, `f` is
locally of finite type, and `f` is a monomorphism. Then `f` is rig-surjective
if and only if every adic morphism `Spf(R) ⟶ Y` from a complete discrete
valuation ring `R` factors through `X`. -/
@[stacks 0AR0]
theorem iff_adicSpf_factors {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Mono f] :
    RigSurjective f ↔
      ∀ sq : AdicSpfSquare f, ∃ lift : sq.specSpf ⟶ X, lift ≫ f = sq.p :=
  sorry

/-- A rig-surjective monomorphism of locally Noetherian formal algebraic spaces
admits a factorization of every adic test map `Spf(R) ⟶ Y` from a complete
discrete valuation ring through the source. -/
theorem exists_factor {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [RigSurjective f] [Mono f]
    (sq : AdicSpfSquare f) :
    ∃ lift : sq.specSpf ⟶ X, lift ≫ f = sq.p :=
  sorry

/-- If every adic test map `Spf(R) ⟶ Y` from a complete discrete valuation ring
factors through `X`, then a locally of finite type morphism of locally
Noetherian formal algebraic spaces is rig-surjective. -/
theorem of_forall_exists_factor {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (h : ∀ sq : AdicSpfSquare f, ∃ lift : sq.specSpf ⟶ X, lift ≫ f = sq.p) :
    RigSurjective f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
