/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import stacks_project.Chap99.Remark_99_7_9_Obstructions_for_quotients_Thickening
public import stacks_project.Chap99.Remark_99_7_9_Obstructions_for_quotients_Obstruction
import StacksCheckRecall

/-!
# Remark 99.7.9 (Obstructions for quotients)

In Situation 99.7.1, if `F` is flat over `B` and `T ⊂ T'` is a first-order thickening
of schemes over `B`, a quotient point `x` of `F_T` has a canonical obstruction class
`o_x(T')` in `Ext¹(K, Q ⊗_{O_T} J)` whose vanishing is equivalent to a lift of `x`
to `Q_{F/X/B}(T')`. Finitely presented points lift to finitely presented points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Remark 99.7.9 (Obstructions for quotients) (1): in Situation 99.7.1, let `T ⊂ T'`
be a first-order thickening of schemes over `B` with ideal sheaf `J`. Then
`X_T ⊂ X_{T'}` is a first-order thickening of algebraic spaces. -/
@[stacks 0CZU] #check instIsFirstOrderThickening_fiberMap

/- Remark 99.7.9 (Obstructions for quotients) (2): the ideal sheaf `I` of
`X_T ⊂ X_{T'}` is a quotient of `f_T^* J`. -/
@[stacks 0CZU] #check instEpi_idealComparison

/-- Remark 99.7.9 (Obstructions for quotients) (3): after the identification of sheaves
on `X_{T'}` with sheaves on `X_T` from More on Morphisms of Spaces, Section 76.9, a
quotient point `x` of `Q_{F/X/B}(T)` given by `0 → K → F_T → Q → 0` determines a
canonical class `o_x(T')` in `Ext¹_{O_{X_T}}(K, Q ⊗_{O_T} J)`. -/
@[stacks 0CZU]
noncomputable def obstruction (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ) :
    Ext (kernel x.map) (tensorIdeal f h x.module) 1 :=
  (canonicalExtension f F h hF x).extClass

/-- The obstruction class `o_x(T')` is the `Ext¹` class of `canonicalExtension`. -/
theorem obstruction_eq (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ) :
    obstruction f F h hF x = (canonicalExtension f F h hF x).extClass :=
  sorry

/-- Kernel-identified quotient points determine isomorphic obstruction classes: `Rel`
supplies an isomorphism of targets from `rel_iso_iff`, hence of kernels and of
`tensorIdeal` coefficients, and the two `Ext¹` classes correspond. -/
theorem obstruction_rel (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) [HasExt.{u} (fiber f σ).Modules]
    {x₁ x₂ : Point f F σ} (hx : Rel x₁ x₂) :
    ∃ (eQ : x₁.module ≅ x₂.module) (eK : kernel x₁.map ≅ kernel x₂.map),
      x₁.map ≫ eQ.hom = x₂.map ∧
        eK.hom ≫ kernel.ι x₂.map = kernel.ι x₁.map ∧
          obstruction f F h hF x₂ =
            (Ext.mk₀ eK.inv).precomp (tensorIdeal f h x₂.module) (zero_add 1)
              ((Ext.mk₀ (tensorIdeal_map f h eQ.hom)).postcomp (kernel x₁.map)
                (add_zero 1) (obstruction f F h hF x₁)) :=
  sorry

/-- Remark 99.7.9 (Obstructions for quotients) (4): the class `o_x(T')` vanishes if
and only if `x` lifts to an element of `Q_{F/X/B}(T')`. -/
@[stacks 0CZU]
theorem obstruction_eq_zero_iff (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) [HasExt.{u} (fiber f σ).Modules]
    (x : Point f F σ) :
    obstruction f F h hF x = 0 ↔ lifts h x :=
  sorry

/-- Remark 99.7.9 (Obstructions for quotients) (5): if `x` is finitely presented as an
element of `Q^{fp}_{F/X/B}(T)`, then any lift to `Q_{F/X/B}(T')` is finitely presented,
by Deformation Theory, Lemma 91.11.3. -/
@[stacks 0CZU]
theorem lift_isFinitePresentation (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (x : FpPoint f F σ) (x' : Point f F σ')
    (hx : Rel (x'.pullback h) x.point) :
    x'.module.IsFinitePresentation :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
