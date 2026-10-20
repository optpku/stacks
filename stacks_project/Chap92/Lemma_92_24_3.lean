module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CotangentComplex.OverRing
import StacksCheckRecall

/-!
# Cotangent complex of a scheme over a ring

Lemma 92.24.3 identifies `L_{X / Spec Λ}` with `L_{𝒪_X / underline{Λ}}` in
`D(𝒪_X)`, where `underline{Λ}` is the constant sheaf with value `Λ` on `X`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 92.24.3. Let `Λ` be a ring. Let `X` be a scheme over `Λ`. Then
`L_{X / Spec Λ} = L_{𝒪_X / underline{Λ}}` where `underline{Λ}` is the constant sheaf
with value `Λ` on `X`. -/
@[stacks 08V6] #check (AlgebraicGeometry.Scheme.Cotangent.overRingIso :
  ∀ (Λ : CommRingCat.{u}) (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec Λ)],
    DerivedCategory.Q.obj
        (AlgebraicGeometry.Scheme.Hom.cotangentComplex
          (X ↘ AlgebraicGeometry.Spec Λ)) ≅
      AlgebraicGeometry.Scheme.Cotangent.constCotangent Λ X)
