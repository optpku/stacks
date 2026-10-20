/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.AffineSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace RingedSpace
namespace ModuleDerived
namespace IsMPseudoCoherent

/- Lemma 37.59.1: for a finite type morphism `f : X ⟶ S` of affine schemes and
`E ∈ D(𝒪_X)`, the derived pushforward of `E` along some closed immersion of `X`
into a finite-dimensional affine space over `S` is `m`-pseudo-coherent if and only if
this holds for every such closed immersion. -/
@[stacks 09VC] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.exists_iff_forall_affineSpace_pushforward :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S]
      [Scheme.Hom.FiniteType f] (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ),
      (∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
        IsClosedImmersion i ∧
          i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f ∧
          IsMPseudoCoherent
            ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m) ↔
        ∀ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
          IsClosedImmersion i →
            i ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = f →
            IsMPseudoCoherent
              ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m)

end IsMPseudoCoherent
end ModuleDerived
end RingedSpace
end AlgebraicGeometry
