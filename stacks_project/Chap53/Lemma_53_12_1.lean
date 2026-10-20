/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Curve.GenericallyEtale
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom.Differentials
open AlgebraicGeometry.RingedSpace.Hom.Differentials.Transitivity
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))}
  [Curve X] [Curve Y] [Smooth X.hom] [Smooth Y.hom]

/- Lemma 53.12.1 (1): for a morphism of smooth curves, the relative differential is nonzero
if and only if `Ω[X/Y]` is supported on a proper closed subset of `X`. -/
@[stacks 0C1C]
#check
  (AlgebraicGeometry.Curve.differentialNonzero_iff_relativeDifferentialsSupportedProper :
    ∀ (f : X ⟶ Y),
    baseChange f.left.toShHom Y.hom.toShHom ≠ 0 ↔
      ∃ Z : Set X.left, IsClosed Z ∧ Z ≠ Set.univ ∧
        moduleSupport Ω[f.left.toShHom] ⊆ Z)

/- Lemma 53.12.1 (2): the relative differentials are supported on a proper closed subset
exactly when the morphism is unramified over some nonempty open subset of the source. -/
/- Lemma 53.12.1 (2) -/
@[stacks 0C1C]
#check
  (AlgebraicGeometry.Curve.relativeDifferentialsSupportedProper_iff_existsUnramifiedRestriction :
    ∀ (f : X ⟶ Y),
    (∃ Z : Set X.left, IsClosed Z ∧ Z ≠ Set.univ ∧
        moduleSupport Ω[f.left.toShHom] ⊆ Z) ↔
      ∃ U : X.left.Opens, Nonempty U ∧
        Unramified (f.left.resLE ⊤ U le_top ≫ Iso.hom (topIso Y.left)))

/- Lemma 53.12.1 (3): the morphism is unramified over some nonempty open subset of the source
if and only if it is étale over some nonempty open subset of the source. -/
/- Lemma 53.12.1 (3) -/
@[stacks 0C1C]
#check
  (AlgebraicGeometry.Curve.existsUnramifiedRestriction_iff_existsEtaleRestriction :
    ∀ (f : X ⟶ Y),
    (∃ U : X.left.Opens, Nonempty U ∧
        Unramified (f.left.resLE ⊤ U le_top ≫ Iso.hom (topIso Y.left))) ↔
      ∃ U : X.left.Opens, Nonempty U ∧
        Etale (f.left.resLE ⊤ U le_top ≫ Iso.hom (topIso Y.left)))

/- Lemma 53.12.1 (4): the morphism is étale over some nonempty open subset of the source
if and only if it induces a finite separable extension `k(X) / k(Y)`. -/
/- Lemma 53.12.1 (4) -/
@[stacks 0C1C]
#check
  (AlgebraicGeometry.Curve.existsEtaleRestriction_iff_finiteSeparableFunctionFieldExtension :
    ∀ (f : X ⟶ Y),
    (∃ U : X.left.Opens, Nonempty U ∧
        Etale (f.left.resLE ⊤ U le_top ≫ Iso.hom (topIso Y.left))) ↔
      ∃ hdom : IsDominant f.left,
        @FiniteFunctionFieldExtension _ _ f.left inferInstance inferInstance hdom ∧
          @Algebra.IsSeparable Y.left.functionField X.left.functionField
            inferInstance inferInstance
            (f.left.functionFieldAlgebra
              (@map_genericPoint_eq_of_isDominant _ _ f.left
                inferInstance inferInstance hdom)))

end AlgebraicGeometry.Curve
