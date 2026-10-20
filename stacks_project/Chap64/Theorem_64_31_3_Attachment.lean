/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.NumberTheory.Automorphic.GaloisRepresentation

/-! Attachment of unramified GL₂ eigenforms to Galois representations. -/

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory Matrix

universe u v

#check (AlgebraicGeometry.SchemeOverField.Eigenform.IsAttachedTo :
    ∀ {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
      {X : SchemeOverField k} [LocallyOfFiniteType X.hom] [ConnectedSpace X.left]
      {xbar : GeometricPoint X.left}
      {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
     (f : Eigenform X (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E),
    Prop)

#check (AlgebraicGeometry.SchemeOverField.Eigenform.isAttachedTo_iff :
    ∀ {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
      {X : SchemeOverField k} [LocallyOfFiniteType X.hom] [ConnectedSpace X.left]
      {xbar : GeometricPoint X.left}
      {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
     (f : Eigenform X (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E),
    f.IsAttachedTo ρ ↔
      ∀ (v : closedPoints X.left)
        (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
          GeometricPoint.finiteFiber xbar),
        algebraMap E (PadicAlgCl ℓ)
            (Matrix.trace (ρ (etaleGeometricFrobenius X xbar v ι)).val) =
          f.t v ∧
        (f.u v).val =
          (residueCard X v : PadicAlgCl ℓ)⁻¹ *
            algebraMap E (PadicAlgCl ℓ)
              (Matrix.det (ρ (etaleGeometricFrobenius X xbar v ι)).val))

#check (AlgebraicGeometry.SchemeOverField.Eigenform.isAttachedTo_t :
    ∀ {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
      {X : SchemeOverField k} [LocallyOfFiniteType X.hom] [ConnectedSpace X.left]
      {xbar : GeometricPoint X.left}
      {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
      {f : Eigenform X (PadicAlgCl ℓ)}
      {ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E}
     (hf : f.IsAttachedTo ρ) (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar),
    f.t v =
      algebraMap E (PadicAlgCl ℓ)
        (Matrix.trace (ρ (etaleGeometricFrobenius X xbar v ι)).val))

#check (AlgebraicGeometry.SchemeOverField.Eigenform.isAttachedTo_u :
    ∀ {k : Type u} [Field k] [Finite k] {ℓ : ℕ} [Fact ℓ.Prime]
      {X : SchemeOverField k} [LocallyOfFiniteType X.hom] [ConnectedSpace X.left]
      {xbar : GeometricPoint X.left}
      {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
      {f : Eigenform X (PadicAlgCl ℓ)}
      {ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E}
     (hf : f.IsAttachedTo ρ) (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar),
    (f.u v).val =
      (residueCard X v : PadicAlgCl ℓ)⁻¹ *
        algebraMap E (PadicAlgCl ℓ)
          (Matrix.det (ρ (etaleGeometricFrobenius X xbar v ι)).val))
