/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Functorial

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FlatPullbackSections

open RingedSpace.ModuleDerived CategoryTheory.HomotopyColimit

/-- Derived global sections over `Spec A`, regarded as an object of `D(A)` through the
canonical isomorphism `A ≅ Γ(Spec A, 𝒪)`. -/
noncomputable def baseSections {A : Type u} [CommRing A] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A)) :
    RingedSpace.ModuleDerived X.toRingedSpace ⥤ DerivedCategory (ModuleCat A) :=
  Modules.Kunneth.globalSectionsOver x ⋙
    ModuleCat.derivedRestrictionOfScalars
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- Evaluating `baseSections x` is derived global sections over the base followed by the
canonical restriction of scalars to `A`. -/
theorem baseSections_obj {A : Type u} [CommRing A] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A))
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    (baseSections x).obj K =
      (ModuleCat.derivedRestrictionOfScalars
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).obj
          ((Modules.Kunneth.globalSectionsOver x).obj K) := sorry

/-- The functor `K ↦ RΓ(U, Lf^*K)` from `D_QCoh(𝒪_X)` to `D(A)`. -/
noncomputable def pullbackFunctor {A : Type u} [CommRing A] {X U : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A)) (f : U ⟶ X) :
    ModuleDerived.Quasicoherent X ⥤ DerivedCategory (ModuleCat A) :=
  ModuleDerived.Quasicoherent.inclusion X ⋙ Modules.Kunneth.pullbackDerived f ⋙
    baseSections (f ≫ x)

/-- Evaluating `pullbackFunctor x f` gives derived pullback along `f` followed by derived
global sections over `A`. -/
theorem pullbackFunctor_obj {A : Type u} [CommRing A] {X U : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A)) (f : U ⟶ X)
    (K : ModuleDerived.Quasicoherent X) :
    (pullbackFunctor x f).obj K =
      (baseSections (f ≫ x)).obj
        ((Modules.Kunneth.pullbackDerived f).obj
          ((ModuleDerived.Quasicoherent.inclusion X).obj K)) := sorry

/-- The sequential functor diagram whose `n`th term sends `K` to
`RΓ(X, RHom(Lₙ, K))`, regarded in `D(A)`. -/
noncomputable def rHomDiagram {A : Type u} [CommRing A] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A))
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (L : ℕᵒᵖ ⥤ RingedSpace.ModuleDerived X.toRingedSpace) :
    ℕ ⥤ (ModuleDerived.Quasicoherent X ⥤ DerivedCategory (ModuleCat A)) :=
  L.rightOp ⋙ MonoidalClosed.internalHom ⋙
    (Functor.whiskeringRight
      (RingedSpace.ModuleDerived X.toRingedSpace)
      (RingedSpace.ModuleDerived X.toRingedSpace)
      (DerivedCategory (ModuleCat A))).obj (baseSections x) ⋙
    (Functor.whiskeringLeft
      (ModuleDerived.Quasicoherent X)
      (RingedSpace.ModuleDerived X.toRingedSpace)
      (DerivedCategory (ModuleCat A))).obj (ModuleDerived.Quasicoherent.inclusion X)

/-- Evaluating `rHomDiagram x L` at `n` and `K` gives derived global sections of the
internal Hom from `Lₙ` to the underlying derived module of `K`. -/
theorem rHomDiagram_obj_obj {A : Type u} [CommRing A] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A))
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (L : ℕᵒᵖ ⥤ RingedSpace.ModuleDerived X.toRingedSpace) (n : ℕ)
    (K : ModuleDerived.Quasicoherent X) :
    ((rHomDiagram x L).obj n).obj K =
      (baseSections x).obj
        (((MonoidalClosed.internalHom).obj (Opposite.op (L.obj (Opposite.op n)))).obj
          ((ModuleDerived.Quasicoherent.inclusion X).obj K)) := sorry

/-- The sequential functor diagram whose `n`th term sends `K` to
`RΓ(X, Eₙ ⊗ᴸ K)`, regarded in `D(A)`. -/
noncomputable def tensorDiagram {A : Type u} [CommRing A] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A))
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [Tensor.Has X.toRingedSpace]
    (E : ℕ ⥤ RingedSpace.ModuleDerived X.toRingedSpace) :
    ℕ ⥤ (ModuleDerived.Quasicoherent X ⥤ DerivedCategory (ModuleCat A)) :=
  E ⋙ Tensor.curried X.toRingedSpace ⋙
    (Functor.whiskeringRight
      (RingedSpace.ModuleDerived X.toRingedSpace)
      (RingedSpace.ModuleDerived X.toRingedSpace)
      (DerivedCategory (ModuleCat A))).obj (baseSections x) ⋙
    (Functor.whiskeringLeft
      (ModuleDerived.Quasicoherent X)
      (RingedSpace.ModuleDerived X.toRingedSpace)
      (DerivedCategory (ModuleCat A))).obj (ModuleDerived.Quasicoherent.inclusion X)

/-- Evaluating `tensorDiagram x E` at `n` and `K` gives derived global sections of
`Eₙ ⊗ᴸ K`. -/
theorem tensorDiagram_obj_obj {A : Type u} [CommRing A] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A))
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [Tensor.Has X.toRingedSpace]
    (E : ℕ ⥤ RingedSpace.ModuleDerived X.toRingedSpace) (n : ℕ)
    (K : ModuleDerived.Quasicoherent X) :
    ((tensorDiagram x E).obj n).obj K =
      (baseSections x).obj
        (Tensor.obj (E.obj n)
          ((ModuleDerived.Quasicoherent.inclusion X).obj K)) := sorry

/-- For a flat finitely presented map `f : U ⟶ X`, with `X` finitely presented over `A`,
there is a direct system `E : ℕ ⥤ D(𝒪_X)` of perfect objects such that
`K ↦ RΓ(U, Lf^*K)` is functorially the sequential homotopy colimit of
`K ↦ RΓ(X, Eₙ ⊗ᴸ K)` in `D(A)`. -/
@[stacks 0CRR]
theorem exists_perfect_tensor {A : Type u} [CommRing A] {X U : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A)) (f : U ⟶ X)
    [Scheme.Hom.FinitePresentation x] [Flat f] [Scheme.Hom.FinitePresentation f]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [Tensor.Has X.toRingedSpace] :
    ∃ E : ℕ ⥤ RingedSpace.ModuleDerived X.toRingedSpace,
      (∀ n : ℕ, IsPerfect (E.obj n)) ∧
        Functorial.IsOf
          (tensorDiagram x E) (pullbackFunctor x f) := sorry

/-- For a flat finitely presented map `f : U ⟶ X`, with `X` finitely presented over `A`,
there is an inverse system `L : ℕᵒᵖ ⥤ D(𝒪_X)` of perfect objects such that
`K ↦ RΓ(U, Lf^*K)` is functorially its sequential `RHom` homotopy-colimit presentation
in `D(A)`. -/
@[stacks 0CRR]
theorem exists_perfect_rHom {A : Type u} [CommRing A] {X U : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of A)) (f : U ⟶ X)
    [Scheme.Hom.FinitePresentation x] [Flat f] [Scheme.Hom.FinitePresentation f]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)] :
    ∃ L : ℕᵒᵖ ⥤ RingedSpace.ModuleDerived X.toRingedSpace,
      (∀ n : ℕ, IsPerfect (L.obj (Opposite.op n))) ∧
        Functorial.IsOf
          (rHomDiagram x L) (pullbackFunctor x f) := sorry

end AlgebraicGeometry.Scheme.FlatPullbackSections
