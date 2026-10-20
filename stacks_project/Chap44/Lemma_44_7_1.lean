/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Galois.Continuity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Galois.Descent

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped MonoidalCategory

universe u

/- Lemma 44.7.1 (1): if a quasi-compact and quasi-separated `k`-scheme `X` has
`k ≃ Γ(X, 𝒪_X)` and a `k`-rational point, then pullback along any Galois extension
`K/k` bijects `X.PicardGroup` with the Galois-fixed Picard classes after base change. -/
@[stacks 0CDT] #check
  (AlgebraicGeometry.FieldExtension.picardPullback_bijOn_fixedPoints :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
      (X : SchemeOverField k) [CompactSpace X.left.carrier]
      [QuasiSeparatedSpace X.left.carrier]
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_point : Nonempty (𝟙_ (SchemeOverField k) ⟶ X)),
      Set.BijOn (Scheme.Hom.picardPullback (FieldExtension.toSource k K X.hom)) Set.univ
        (AlgebraicGeometry.FieldExtension.Picard.galoisFixedSubgroup k K X.hom : Set _))

/- Lemma 44.7.1 (2): under the same hypotheses, the Galois action on the Picard group after
base change is continuous for the Krull topology on `Gal(K/k)` and the discrete topology on
the Picard group. -/
@[stacks 0CDT] #check
  (AlgebraicGeometry.FieldExtension.continuous_picardAction :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [IsGalois k K]
      (X : SchemeOverField k) [CompactSpace X.left.carrier]
      [QuasiSeparatedSpace X.left.carrier]
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_point : Nonempty (𝟙_ (SchemeOverField k) ⟶ X)),
      Continuous (AlgebraicGeometry.FieldExtension.Picard.galoisActionMap k K X.hom))
