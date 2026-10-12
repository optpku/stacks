/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyB
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty
open CategoryTheory.Limits

universe u

/- Lemma 59.43.2: if every étale covering of every base change admits the
stated étale neighbourhood, coproduct decomposition, and factoring maps at
each point, then `f` has property (B). -/
@[stacks 04DP] #check (AlgebraicGeometry.hasPropertyB_of_localDecomposition :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (V : Y.Etale)
      (𝒰 : (pullback f V.hom).Cover.{u} (precoverage @Etale))
      (v : V.left),
      ∃ (V' : V.left.Etale) (v' : V'.left),
        V'.hom.base v' = v ∧
          ∃ (W : 𝒰.I₀ → Scheme.{u})
            (d : (∐ W) ≅ pullback f (V'.hom ≫ V.hom)),
            ∀ i : 𝒰.I₀,
              ∃ (m : W i ⟶ 𝒰.X i),
                m ≫ 𝒰.f i =
                  (Sigma.ι W i ≫ d.hom) ≫
                    Scheme.Pullback.baseChangeMap f V.hom V'.hom),
    AlgebraicGeometry.hasPropertyB f)
