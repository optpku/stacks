/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.AbsoluteNoetherianApproximation
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 32.5.3: a quasi-compact quasi-separated scheme containing a quasi-compact open which
is an absolute Noetherian inverse limit admits a compatible absolute Noetherian approximation. -/
@[stacks 07RN] #check
  (AlgebraicGeometry.exists_absoluteNoetherianApproximation_of_compactOpen_inverseLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
      (V : S.Opens) (hV : IsCompact (V : Set S))
      (D : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (cV : Cone (D ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))))
      (hcV : IsLimit cV)
      (eV : V.toScheme ≅ cV.pt)
      (hDaffine :
        ∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii')).left)
      (hDfinite : ∀ i : I, Scheme.Hom.FiniteType (D.obj i).hom),
      Nonempty (CompactOpenAbsoluteNoetherianApproximation S V D cV eV))
