/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.ClosedVanishing
import StacksCheckRecall

/-!
# Making a map of quasi-coherent modules vanish on a closed subscheme

Over an affine base, vanishing of a quasi-coherent map after quasi-compact base change
is witnessed by a closed subscheme of the base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.8.2 (1): Vanishing after quasi-compact base change is witnessed by a
closed subscheme through which the base change factors. -/
@[stacks 083K]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_closedImmersion_of_baseChangeMap_eq_zero :
  ∀ {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} {ℱ 𝒢 : X.Modules}
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
    (hG_flat : flatOver 𝒢 (SchemeRealization.toBase X)) (u : ℱ ⟶ 𝒢)
    {T : Scheme.{u}} (g : T ⟶ S) [AlgebraicGeometry.QuasiCompact g]
    (hu : baseChangeMap (SchemeRealization.toBase X)
      (ofOverHomMk g (Category.comp_id g)) u = 0),
    ∃ Z : Over S, AlgebraicGeometry.IsClosedImmersion Z.hom ∧
      Nonempty (Over.mk g ⟶ Z) ∧
        baseChangeMap (SchemeRealization.toBase X)
          (ofOverHomMk Z.hom (Category.comp_id Z.hom)) u = 0)

/- Lemma 77.8.2 (2): Finite type and quasi-compact scheme-theoretic support allow
the closed subscheme to be taken of finite presentation. -/
@[stacks 083K]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.exists_closedImmersion_of_baseChangeMap_eq_zero_of_finitePresentation :
  ∀ {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} {ℱ 𝒢 : X.Modules}
    [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] [ℱ.IsFiniteType]
    [IsQuasiCompact (schemeTheoreticSupport ℱ).X]
    (hG_flat : flatOver 𝒢 (SchemeRealization.toBase X)) (u : ℱ ⟶ 𝒢)
    {T : Scheme.{u}} (g : T ⟶ S) [AlgebraicGeometry.QuasiCompact g]
    (hu : baseChangeMap (SchemeRealization.toBase X)
      (ofOverHomMk g (Category.comp_id g)) u = 0),
    ∃ Z : Over S,
      (AlgebraicGeometry.IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom) ∧
        Nonempty (Over.mk g ⟶ Z) ∧
          baseChangeMap (SchemeRealization.toBase X)
            (ofOverHomMk Z.hom (Category.comp_id Z.hom)) u = 0)

end AlgebraicGeometry.AlgebraicSpace.Modules
