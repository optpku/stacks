module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Etale
import StacksCheckRecall

/-!
# Étale covering of relative Hom

If `Z ⟶ B` is finite locally free and `X' ⟶ X` is étale over `B`, then
`Mor_B(Z, X') ⟶ Mor_B(Z, X)` is representable by algebraic spaces and étale,
and is surjective when `X' ⟶ X` is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

universe u

/- Lemma 97.10.3 (1): let `S` be a scheme and let `Z ⟶ B` and `X' ⟶ X ⟶ B` be
morphisms of algebraic spaces over `S`. If `X' ⟶ X` is étale and `Z ⟶ B` is
finite locally free, then `Mor_B(Z, X') ⟶ Mor_B(Z, X)` is representable by
algebraic spaces and étale. -/
@[stacks 05Y5] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.postcomp_etale :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X' X : Over B} (f : X' ⟶ X) [Etale f.left] [FiniteLocallyFree Z.hom]
    (U : Over S) (ξ : Pair Z.hom X.hom U),
    ∃ (F : AlgebraicSpace S) (p : F ⟶ ofOver U)
      (q : toSheaf.obj F ⟶ sheaf Z.hom X'.hom),
      Etale p ∧
        IsPullback q (toSheaf.map p) (postcompose f)
          (SpacePair.toSheafHom ((SpacePair.schemeEquiv Z X U).symm ξ)))

/- Lemma 97.10.3 (2): if in addition `X' ⟶ X` is surjective, then
`Mor_B(Z, X') ⟶ Mor_B(Z, X)` is surjective. -/
@[stacks 05Y5] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.postcomp_surjective :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X' X : Over B} (f : X' ⟶ X) [Etale f.left] [FiniteLocallyFree Z.hom]
    [Surjective f.left] (U : Over S) (ξ : Pair Z.hom X.hom U),
    ∃ (F : AlgebraicSpace S) (p : F ⟶ ofOver U)
      (q : toSheaf.obj F ⟶ sheaf Z.hom X'.hom),
      Etale p ∧ Surjective p ∧
        IsPullback q (toSheaf.map p) (postcompose f)
          (SpacePair.toSheafHom ((SpacePair.schemeEquiv Z X U).symm ξ)))
