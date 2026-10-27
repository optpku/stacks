/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FormalGlueing.Equivalence
import StacksCheckRecall

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

/- Proposition 81.10.9 (1): In Situation 81.10.6 the functor sending `F` to
`(F|_U, f^* F, can)` is an equivalence `QCoh X ⥤ category f i`. -/
@[stacks 0AF0]
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.functor_isEquivalence :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i], (functor f i).IsEquivalence)

/- Proposition 81.10.9 (2): In Situation 81.10.6 the quasi-inverse of this
glueing functor is the reverse functor sending `(H, G, φ)` to
`kernel (j_* H ⊞ f_* G ⟶ (f ∘ j')_* (G|_V))`. -/
@[stacks 0AF0]
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.reverse_isQuasiInverse :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i], (functor f i).IsQuasiInverse (reverse f i))

/- The unit of `functor ⊣ reverse` is an isomorphism (the source map `α`). -/
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.unit_isIso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i], IsIso (unit f i))

/- The counit of `functor ⊣ reverse` is an isomorphism (the source maps `β`
and `γ`). -/
#check (AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing.counit_isIso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i], IsIso (counit f i))

end FormalGlueing
end AlgebraicGeometry.AlgebraicSpace.QCoh
