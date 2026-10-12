/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.GaloisCover.Fpqc

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace Scheme
namespace QCoh
namespace GaloisDescent

/- Lemma 35.6.2: for a surjective finite étale morphism whose orbit map is an
isomorphism, pullback identifies quasi-coherent modules on `Y` with pullback-twisted
`G`-equivariant quasi-coherent modules on `X`. -/
@[stacks 0D1V] #check
  (AlgebraicGeometry.Scheme.QCoh.GaloisDescent.descentIsEquivalence :
    ∀ {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}} (p : X ⟶ Y)
      (rho : Gᵐᵒᵖ →* Aut (Over.mk p : Over Y)) [IsFinite p] [Etale p] [Surjective p]
      [IsIso (orbitMap p rho)],
      (descent p rho).IsEquivalence)

end GaloisDescent
end QCoh
end Scheme
end AlgebraicGeometry
