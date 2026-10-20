module

public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import stacks_project.Chap81.Lemma_81_10_7_Reverse
public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing

/-!
# Proposition 81.10.9

In Situation 81.10.6, the canonical glueing functor `QCoh X ⥤ category f i`
is an equivalence of categories, with quasi-inverse the reverse kernel functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh
namespace FormalGlueing

/-- Proposition 81.10.9 (1): In Situation 81.10.6 the functor sending `F` to
`(F|_U, f^* F, can)` is an equivalence `QCoh X ⥤ category f i`. -/
@[stacks 0AF0, instance]
instance functor_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (functor f i).IsEquivalence :=
  sorry

/-- Proposition 81.10.9 (2): In Situation 81.10.6 the quasi-inverse of this
glueing functor is the reverse functor sending `(H, G, φ)` to
`kernel (j_* H ⊞ f_* G ⟶ (f ∘ j')_* (G|_V))`. -/
@[stacks 0AF0]
theorem reverse_isQuasiInverse {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (functor f i).IsQuasiInverse (reverse f i) :=
  sorry

/-- The unit of `functor ⊣ reverse` is an isomorphism (the source map `α`). -/
instance unit_isIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    IsIso (unit f i) :=
  sorry

/-- The counit of `functor ⊣ reverse` is an isomorphism (the source maps `β`
and `γ`). -/
instance counit_isIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    IsIso (counit f i) :=
  sorry

end FormalGlueing
end AlgebraicGeometry.AlgebraicSpace.QCoh
