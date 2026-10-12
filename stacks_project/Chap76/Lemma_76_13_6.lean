/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting.EtaleSurjective
import StacksCheckRecall

/-!
# Étale-on-top permanence for formally smooth, étale, and unramified transformations

If `a : F ⟶ G` is a representable, surjective, and étale transformation of
functors on `(Sch/S)_fppf`, then formal smoothness, étaleness, or unramifiedness
of `b : G ⟶ H` passes to `a ≫ b`. Conversely, formal smoothness of `a ≫ b`
yields an étale affine local lift against an affine first-order thickening, while
formal unramifiedness or étaleness of `a ≫ b` implies the same property of `b`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Over

universe u

/- Lemma 76.13.6 (1): If `a : F ⟶ G` is a representable, surjective, and étale
transformation of functors on `(Sch/S)_fppf` and `b : G ⟶ H` is formally
smooth, then `a ≫ b` (source `b ∘ a`) is formally smooth. -/
@[stacks 04CY]
#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.precomp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
      (MorphismProperty.over (@Etale ⊓ @Surjective)).presheaf a →
        FormallySmooth b → FormallySmooth (a ≫ b))

/- Lemma 76.13.6 (2): If `a : F ⟶ G` is a representable, surjective, and étale
transformation of functors on `(Sch/S)_fppf` and `b : G ⟶ H` is formally
étale, then `a ≫ b` (source `b ∘ a`) is formally étale. -/
@[stacks 04CY]
#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.precomp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
      (MorphismProperty.over (@Etale ⊓ @Surjective)).presheaf a →
        FormallyEtale b → FormallyEtale (a ≫ b))

/- Lemma 76.13.6 (3): If `a : F ⟶ G` is a representable, surjective, and étale
transformation of functors on `(Sch/S)_fppf` and `b : G ⟶ H` is formally
unramified, then `a ≫ b` (source `b ∘ a`) is formally unramified. -/
@[stacks 04CY]
#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified.precomp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
      (MorphismProperty.over (@Etale ⊓ @Surjective)).presheaf a →
        FormallyUnramified b → FormallyUnramified (a ≫ b))

/- Lemma 76.13.6 (4): If `a ≫ b` is formally smooth, then a solid square against
an affine first-order thickening lifts étale-locally on `T'` through an affine
étale morphism `U' ⟶ T'` covering the image of any given point of `T`. -/
@[stacks 04CY]
#check (AlgebraicGeometry.Scheme.Over.FormallySmooth.exists_etaleAffineLocalLift :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
      (MorphismProperty.over (@Etale ⊓ @Surjective)).presheaf a →
        ∀ [FormallySmooth (a ≫ b)] {T T' : Over S} [IsAffine T.left]
          [IsAffine T'.left] (i : T ⟶ T') [IsFirstOrderThickening i.left]
          (x : G.obj (op T)) (y : H.obj (op T')),
          b.app (op T) x = H.map (op i) y →
            ∀ t : T.left, ∃ (U' : Over S) (π : U' ⟶ T') (z : G.obj (op U')),
              FormallySmooth.IsEtaleAffineLocalLift b i π x y z t)

/- Lemma 76.13.6 (5): If `a ≫ b` is formally unramified and `a` is representable,
surjective, and étale, then `b` is formally unramified. -/
@[stacks 04CY]
#check (AlgebraicGeometry.Scheme.Over.FormallyUnramified.of_precomp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
      (MorphismProperty.over (@Etale ⊓ @Surjective)).presheaf a →
        FormallyUnramified (a ≫ b) → FormallyUnramified b)

/- Lemma 76.13.6 (6): If `a ≫ b` is formally étale and `a` is representable,
surjective, and étale, then `b` is formally étale. -/
@[stacks 04CY]
#check (AlgebraicGeometry.Scheme.Over.FormallyEtale.of_precomp :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) (b : G ⟶ H),
      (MorphismProperty.over (@Etale ⊓ @Surjective)).presheaf a →
        FormallyEtale (a ≫ b) → FormallyEtale b)
