/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.NumberTheory.Automorphic.CuspForms.Finiteness
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open scoped TensorProduct

universe u v

/- Proposition 64.31.5 (1). Fixed-character cusp forms over a Noetherian
coefficient ring form a finitely generated module. -/
@[stacks 03VW] #check (AlgebraicGeometry.SchemeOverField.CuspForms.moduleFinite :
  ∀ {k : Type u} [Field k] [Fintype k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    {Λ : Type v} [CommRing Λ] [Invertible (ringChar k : Λ)] [IsNoetherianRing Λ]
    (character : closedPoints X.left → Λˣ), Module.Finite Λ (CuspForms X Λ character))

/- Proposition 64.31.5 (2). For a prime-subfield-valued character, the canonical
scalar-extension map to a coefficient field is bijective. -/
@[stacks 03VW] #check (AlgebraicGeometry.SchemeOverField.CuspForms.baseChange_bijective :
  ∀ {k : Type u} [Field k] [Fintype k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace X.left]
    {Λ : Type v} [Field Λ] [Invertible (ringChar k : Λ)]
    (character : closedPoints X.left → (⊥ : Subfield Λ)ˣ),
    Function.Bijective
      (CuspForms.baseChange character :
        Λ ⊗[(⊥ : Subfield Λ)] CuspForms X (⊥ : Subfield Λ) character →ₗ[Λ]
          CuspForms X Λ
            (Units.map (algebraMap (⊥ : Subfield Λ) Λ).toMonoidHom ∘ character)))

/- Proposition 64.31.5 (3). Scalar extension intertwines every Hecke operator. -/
@[stacks 03VW] #check (AlgebraicGeometry.SchemeOverField.CuspForms.baseChange_heckeT :
  ∀ {k : Type u} [Field k] [Fintype k]
    {Λ : Type v} [CommRing Λ] [Invertible (ringChar k : Λ)] {X : SchemeOverField k}
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    {F : Type v} [CommRing F] [Invertible (ringChar k : F)] [Algebra F Λ]
    (character : closedPoints X.left → Fˣ) (place : closedPoints X.left),
    CuspForms.heckeT (Units.map (algebraMap F Λ).toMonoidHom ∘ character) place ∘ₗ
        CuspForms.baseChange character =
      CuspForms.baseChange character ∘ₗ LinearMap.baseChange Λ (CuspForms.heckeT character place))
