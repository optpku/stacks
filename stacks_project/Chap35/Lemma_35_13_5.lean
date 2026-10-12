/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EffectiveEpi.Submersive
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace CategoryTheory.SemiRepresentableFamily.Over

/- Lemma 35.13.5: an affine universally effective epimorphic family whose coproduct map is
submersive after every affine base change is universally effective epimorphic as a family of
schemes. -/
@[stacks 0EUD] #check
  (@CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily.forgetToScheme :
    ∀ {X : AffineScheme.{u}} (K : Over.{u} X),
      IsUniversalEffectiveEpiFamily K →
        (∀ (Y : AffineScheme.{u}) (f : Y ⟶ X),
          AlgebraicGeometry.Submersive (Limits.Sigma.desc
            (fun i : K.index ↦
              AffineScheme.forgetToScheme.map ((K.baseChange f).obj i).hom))) →
          IsUniversalEffectiveEpiFamily
            (ofArrows
              (fun i : K.index ↦ AffineScheme.forgetToScheme.obj (K.obj i).left)
              (fun i : K.index ↦ AffineScheme.forgetToScheme.map (K.obj i).hom)))

end CategoryTheory.SemiRepresentableFamily.Over
