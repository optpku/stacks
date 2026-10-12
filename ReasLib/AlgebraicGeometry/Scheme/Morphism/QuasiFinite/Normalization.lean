/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

/-!
# The quasi-finite locus in the relative normalization

This file relates the quasi-finite locus of a separated finite-type scheme morphism to an open
subscheme of its relative normalization.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A separated finite-type morphism restricts to an isomorphism over an open of its relative
normalization whose inverse image is exactly its quasi-finite locus. -/
theorem FiniteType.exists_isIso_morphismRestrict_toNormalization
    [FiniteType f] [IsSeparated f] :
    ∃ U' : f.normalization.Opens,
      IsIso (f.toNormalization ∣_ U') ∧
        ((f.toNormalization ⁻¹ᵁ U' : X.Opens) : Set X) =
          {x : X | f.QuasiFiniteAt x} := sorry

/-- A quasi-finite separated morphism of schemes is quasi-affine. -/
theorem QuasiFinite.quasiAffine [QuasiFinite f] [IsSeparated f] : QuasiAffineHom f := sorry

end Scheme.Hom
end AlgebraicGeometry
