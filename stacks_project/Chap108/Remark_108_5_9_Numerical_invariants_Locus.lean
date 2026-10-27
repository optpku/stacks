/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Numerical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.Flat
public import stacks_project.Chap99.«99_8_1_1_Functor»

/-! # Numerical Quot loci and the legacy schemes-over interface -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Flatness of a presheaf morphism on schemes over an algebraic space. -/
abbrev IsFlatOnSchemesOver {F G : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop := SchemeOver.IsFlat φ

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.isFlat_iff :
  ∀ {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G),
    SchemeOver.IsFlat φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          CategoryTheory.IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.Flat snd.left.left)

variable (f : X ⟶ B) [FinitePresentation f] [Separated f]
variable (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
variable (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i))

#check (AlgebraicGeometry.AlgebraicSpace.Quot.quotNumerical f F E P hE : Subfunctor (quot f F))

#check (AlgebraicGeometry.AlgebraicSpace.Quot.quotNumericalι f F E P hE :
  (quotNumerical f F E P hE).toFunctor ⟶ quot f F)

variable (L : X.Modules) [isInvertibleObject L] (Pℤ : ℤ → ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Quot.invertiblePowerFamily L :
  ULift.{u, 0} ℤ → ModuleDerived X)

#check (AlgebraicGeometry.AlgebraicSpace.Quot.quotNumericalHilbert f F L Pℤ : Subfunctor (quot f F))

end AlgebraicGeometry.AlgebraicSpace.Quot
