/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Map

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Property (B): every étale covering after base change along an étale object
admits an étale covering of the base whose pullbacks decompose into pieces
factoring through the original covering. -/
def hasPropertyB {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (V : Y.Etale) (𝒰 : (pullback f V.hom).Cover.{u} (precoverage @Etale)),
    ∃ (𝒱 : V.left.Cover.{u} (precoverage @Etale)),
      ∀ j : 𝒱.I₀,
        ∃ (W : 𝒰.I₀ → Scheme.{u})
          (d : (∐ W) ≅ pullback f (𝒱.f j ≫ V.hom)),
          ∀ i : 𝒰.I₀,
            ∃ (m : W i ⟶ 𝒰.X i),
              m ≫ 𝒰.f i =
                (Sigma.ι W i ≫ d.hom) ≫
                  Scheme.Pullback.baseChangeMap f V.hom (𝒱.f j)

/-- Property (B) is equivalent to its explicit cover-and-coproduct
characterization. -/
theorem hasPropertyB_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    hasPropertyB f ↔
      ∀ (V : Y.Etale) (𝒰 : (pullback f V.hom).Cover.{u} (precoverage @Etale)),
        ∃ (𝒱 : V.left.Cover.{u} (precoverage @Etale)),
          ∀ j : 𝒱.I₀,
            ∃ (W : 𝒰.I₀ → Scheme.{u})
              (d : (∐ W) ≅ pullback f (𝒱.f j ≫ V.hom)),
              ∀ i : 𝒰.I₀,
                ∃ (m : W i ⟶ 𝒰.X i),
                  m ≫ 𝒰.f i =
                    (Sigma.ι W i ≫ d.hom) ≫
                      Scheme.Pullback.baseChangeMap f V.hom (𝒱.f j) := sorry

/-- A pointwise étale-neighbourhood decomposition criterion implies Property
(B). -/
theorem hasPropertyB_of_localDecomposition
    {X Y : Scheme.{u}} (f : X ⟶ Y)
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
                    Scheme.Pullback.baseChangeMap f V.hom V'.hom) :
    hasPropertyB f := sorry

/-- Every finite morphism of schemes has Property (B). -/
theorem hasPropertyB_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] :
    hasPropertyB f := sorry

/-- Every integral morphism of schemes has Property (B). -/
theorem hasPropertyB_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] : hasPropertyB f := sorry

end AlgebraicGeometry
