module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.OverRing
import StacksCheckRecall

/-!
# Cotangent complex of an algebraic space over a ring

Lemma 92.26.4 identifies `L_{X / Spec Λ}` with `L_{𝒪_X / underline{Λ}}` in
`D(𝒪_X)`, where `underline{Λ}` is the constant sheaf with value `Λ` on `X_étale`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

noncomputable section

universe u

/- Lemma 92.26.4. Let `Λ` be a ring. Let `X` be an algebraic space over `Λ`. Then
`L_{X / Spec Λ} = L_{𝒪_X / underline{Λ}}` where `underline{Λ}` is the constant sheaf
with value `Λ` on `X_étale`. -/
@[stacks 08VG] #check (AlgebraicGeometry.AlgebraicSpace.Cotangent.spaceOverRingIso :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
    AlgebraicGeometry.AlgebraicSpace.Cotangent.cotangent
        (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase X) ≅
      AlgebraicGeometry.AlgebraicSpace.Cotangent.constCotangent Λ X)

#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.spaceOverRingIso_hom :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ)),
    (AlgebraicGeometry.AlgebraicSpace.Cotangent.spaceOverRingIso Λ X).hom =
      inv (AlgebraicGeometry.AlgebraicSpace.Cotangent.spaceOverRingCompare Λ X))
