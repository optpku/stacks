module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Restriction
import StacksCheckRecall

/-!
# Lemma 62.6.15

Restriction of relative cycles to an open of the source whose complement is
fibrewise of dimension less than `r`.
-/

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 62.6.15: if `S` is locally Noetherian, `f : X ⟶ S` is locally of
finite type, `r ≥ 0`, and `U ⊆ X` is open with `dim(X_s \ U_s) < r` for every
`s ∈ S`, then restriction is a bijection `z(X/S, r) → z(U/S, r)`. -/
@[stacks 0H5F] #check (AlgebraicGeometry.RelativeCycle.groupRestrict_bijective :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (U : X.Opens) (r : ℕ),
    AlgebraicGeometry.RelativeCycle.fiberOpenComplementDimensionLT f U r →
      Function.Bijective (AlgebraicGeometry.RelativeCycle.groupRestrict f U r))
