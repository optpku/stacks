module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.AffineCompletion
public import ReasLib.AlgebraicGeometry.FormalSpectrum.PowerStages
import StacksCheckRecall

/-!
# Affine formal completions along a closed subset

The source-facing entries below retain the three clauses of the formal
completion result while the reusable constructions are owned by `ReasLib`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/- Lemma 87.14.6 (1): If `X \ T` is quasi-compact, then the formal completion
   of `X = Spec(A)` along `T` is adic*. -/
@[stacks 0GBA] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.isAdicStar_completionAlong_of_isCompact_compl :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A]
      (structureHom : Spec (.of A) ⟶ S)
      (T : Closeds (Spec (.of A)))
      (hT : IsCompact (T : Set (Spec (.of A)))ᶜ),
      FormalAlgebraicSpace.IsAdicStarAffine (affineCompletionAlong structureHom T))

/- Lemma 87.14.6 (2): If `T = V(I)` for a finitely generated ideal `I`, then
   the formal completion is `Spf` of the `I`-adic completion. -/
@[stacks 0GBA] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.isIso_completionSpfToCompletionAlong_of_fg :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A]
      (structureHom : Spec (.of A) ⟶ S)
      (I : Ideal A) (hI : I.FG)
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
      IsIso (AlgebraicGeometry.AffineFormalAlgebraicSpace.completionSpfToCompletionAlong
        structureHom I))

/- Lemma 87.14.6 (3): If `X = Spec(A)` is Noetherian, then the formal
   completion of `X` along `T` is Noetherian. -/
@[stacks 0GBA] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.isNoetherian_completionAlong :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A]
      [IsNoetherian (Spec (.of A))]
      (structureHom : Spec (.of A) ⟶ S)
      (T : Closeds (Spec (.of A))),
      FormalAlgebraicSpace.IsNoetherianAffine (affineCompletionAlong structureHom T))

end AlgebraicGeometry.AffineFormalAlgebraicSpace
