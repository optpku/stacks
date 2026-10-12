/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Normalization

/-!
# Factorizations of quasi-finite morphisms

A quasi-finite morphism between affine schemes factors through an affine scheme as an open
immersion followed by a finite morphism. More generally, a separated quasi-finite morphism to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion followed by a
finite morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A quasi-finite morphism between affine schemes factors as an open immersion into an affine
scheme followed by a finite morphism. -/
theorem exists_affine_openImmersion_finiteFactorization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] [IsAffine Y] [QuasiFinite f] :
    ∃ (Z : Scheme.{u}) (j : Y ⟶ Z) (π : Z ⟶ X),
      IsAffine Z ∧ IsOpenImmersion j ∧ IsFinite π ∧ j ≫ π = f := sorry

namespace QuasiFinite

/-- A separated quasi-finite morphism to a quasi-compact quasi-separated scheme factors as a
quasi-compact open immersion followed by a finite morphism. -/
@[stacks 05K0]
theorem exists_openImmersion_finiteFactorization
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiFinite f] [IsSeparated f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (T : Scheme.{u}) (j : X ⟶ T) (π : T ⟶ S),
      QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧ j ≫ π = f := sorry

end QuasiFinite

end AlgebraicGeometry.Scheme.Hom
