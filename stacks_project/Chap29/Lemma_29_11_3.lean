/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.11.3 (1): a morphism of schemes is affine if and only if the target admits an
affine open cover whose pullback pieces are affine. -/
@[stacks 01S8] #check
  (@AlgebraicGeometry.isAffineHom_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      IsAffineHom f ↔
        ∃ 𝒰 : S.AffineOpenCover.{u},
          ∀ i : 𝒰.I₀, IsAffine ((𝒰.openCover.pullback₁ f).X i))

/- Lemma 29.11.3 (2): a morphism of schemes is affine if and only if it is isomorphic over the
target to a relative spectrum of a quasi-coherent algebra sheaf. -/
@[stacks 01S8] #check
  (@AlgebraicGeometry.Scheme.isAffineHom_iff_exists_iso_relativeSpec :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      IsAffineHom f ↔
        ∃ (A : S.QcAlgebraUnder) (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
          AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P ∧
            Nonempty (Over.mk f ≅ Over.mk (AlgebraicGeometry.Scheme.relativeSpecπ P)))

/- Lemma 29.11.3 (3): for an affine morphism, the canonical morphism to the relative spectrum
of the pushed-forward structure sheaf is an isomorphism. -/
@[stacks 01S8] #check
  (@AlgebraicGeometry.Scheme.isIso_pushforwardStructureSheafRelativeSpectrumHom :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver
        (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f))
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      IsIso (AlgebraicGeometry.Scheme.pushforwardStructureSheafRelativeSpectrumHom f P))
