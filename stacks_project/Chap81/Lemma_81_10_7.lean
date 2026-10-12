/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap81.Lemma_81_10_7_Reverse
public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing

/-!
# Lemma 81.10.7

In Situation 81.10.6, the reverse functor sending a glueing triple
`(H, G, φ)` to the kernel of `j_* H ⊞ f_* G ⟶ (f ∘ j')_* (G|_V)` is
right adjoint to the canonical glueing functor sending `F` to
`(F|_U, f^* F, can)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh
namespace FormalGlueing

/-- Lemma 81.10.7: In Situation 81.10.6, the reverse functor sending a triple
`(H, G, φ)` to `kernel (j_* H ⊞ f_* G ⟶ (f ∘ j')_* (G|_V))` is right adjoint
to the canonical glueing functor sending `F` to `(F|_U, f^* F, can)`. -/
@[stacks 0AEY]
def functorReverseAdjunction {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    functor f i ⊣ reverse f i where
  unit := unit f i
  counit := counit f i
  left_triangle_components := sorry
  right_triangle_components := sorry

/-- The unit of `functorReverseAdjunction` is the reverse-kernel unit. -/
theorem functorReverseAdjunction_unit {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    (functorReverseAdjunction f i).unit = unit f i :=
  rfl

/-- The counit of `functorReverseAdjunction` is the reverse-kernel counit. -/
theorem functorReverseAdjunction_counit {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    (functorReverseAdjunction f i).counit = counit f i :=
  rfl

/-- The canonical glueing functor is a left adjoint, with right adjoint
`reverse`. -/
instance functor_isLeftAdjoint {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    (functor f i).IsLeftAdjoint :=
  ⟨reverse f i, ⟨functorReverseAdjunction f i⟩⟩

/-- The reverse functor is a right adjoint, with left adjoint `functor`. -/
instance reverse_isRightAdjoint {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    (reverse f i).IsRightAdjoint :=
  ⟨functor f i, ⟨functorReverseAdjunction f i⟩⟩

end FormalGlueing
end AlgebraicGeometry.AlgebraicSpace.QCoh
