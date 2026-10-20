module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.13.7 (1): from an affine source, quasi-affineness is equivalent to
quasi-compactness. -/
@[stacks 01SP] #check
  (AlgebraicGeometry.quasiAffineHom_iff_quasiCompact_of_isAffine :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X],
      QuasiAffineHom f ↔ QuasiCompact f)

/- Lemma 29.13.7 (2): a morphism from an affine scheme to a quasi-separated
scheme is quasi-affine. -/
@[stacks 01SP] #check
  (AlgebraicGeometry.quasiAffineHom_of_isAffine_of_quasiSeparated :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [QuasiSeparatedSpace S],
      QuasiAffineHom f)
