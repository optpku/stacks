module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Sheaf

/-!
# Characterization of sheaves on the big ph site of an algebraic space

A presheaf on `(Spaces/X)_ph` is a sheaf if and only if it satisfies the sheaf
condition for étale coverings and the proper-surjective equalizer condition.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 73.8.7: let `S` be a scheme, let `X` be an algebraic space over `S`,
and let `F` be a presheaf on `(Spaces/X)_ph`. Then `F` is a sheaf if and only
if `F` satisfies the sheaf condition for étale coverings, and if
`f : V ⟶ U` is a proper surjective morphism of `(Spaces/X)_ph`, then `F(U)`
maps bijectively to the equalizer of the two maps `F(V) ⟶ F(V ×_U V)`. -/
@[stacks 0DFM] #check (AlgebraicGeometry.AlgebraicSpace.Ph.Sheaf.iffEtaleAndEqualizer :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : (Over X)ᵒᵖ ⥤ Type v),
    Presheaf.IsSheaf (bigPhSite X) F ↔
      Presheaf.IsSheaf
          ((etalePrecoverage : Precoverage (AlgebraicSpace S)).toGrothendieck.over X) F ∧
        Ph.Equalizer.IsProperSurjective F)
