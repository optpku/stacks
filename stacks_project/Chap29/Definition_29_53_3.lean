module

public import Mathlib.AlgebraicGeometry.Normalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]

/- Definition 29.53.3: for a quasi-compact and quasi-separated morphism `f : Y ⟶ X`, the
normalization of `X` in `Y` is `f.normalization`. -/
@[stacks 035H] #check (AlgebraicGeometry.Scheme.Hom.normalization f : Scheme.{u})

/- The canonical map from `Y` to the relative normalization. -/
@[stacks 035H] #check (AlgebraicGeometry.Scheme.Hom.toNormalization f :
  Y ⟶ AlgebraicGeometry.Scheme.Hom.normalization f)

/- The canonical map from the relative normalization to `X`. -/
@[stacks 035H] #check (AlgebraicGeometry.Scheme.Hom.fromNormalization f :
  AlgebraicGeometry.Scheme.Hom.normalization f ⟶ X)

/- The canonical maps through the relative normalization factor `f`. -/
@[stacks 035H] #check (AlgebraicGeometry.Scheme.Hom.toNormalization_fromNormalization f :
  AlgebraicGeometry.Scheme.Hom.toNormalization f ≫
    AlgebraicGeometry.Scheme.Hom.fromNormalization f = f)

/- On every affine open `U ⊆ X`, sections of the relative normalization over the inverse image
are isomorphic to the corresponding integral closure. -/
variable {U : X.Opens} (hU : IsAffineOpen U)

#check (AlgebraicGeometry.Scheme.Hom.normalizationObjIso f hU :
  -- Local instance justification (defeq pin): `normalizationObjIso` defines
  -- `integralClosure` using the `Algebra` induced by
  -- `(f.app U).hom`.
  letI := (f.app U).hom.toAlgebra
  Γ(AlgebraicGeometry.Scheme.Hom.normalization f,
      AlgebraicGeometry.Scheme.Hom.fromNormalization f ⁻¹ᵁ U) ≅
    CommRingCat.of (integralClosure Γ(X, U) Γ(Y, f ⁻¹ᵁ U)))

end AlgebraicGeometry.Scheme.Hom
