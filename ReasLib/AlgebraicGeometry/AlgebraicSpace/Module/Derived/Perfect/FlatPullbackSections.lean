/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.OverAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Functorial
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal

/-!
# Functorial sequential presentations of flat finitely presented pullback sections

For a flat morphism `f : U ⟶ X` of algebraic spaces of finite presentation over a
ring `A`, the functor `K ↦ RΓ(U, Lf^* K)` from `D_QCoh(𝒪_X)` to `D(A)` is a
sequential homotopy colimit of internal-Hom diagrams and of derived-tensor diagrams
in perfect objects of `D(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Functor
open CategoryTheory.HomotopyColimit CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FlatPullbackSections

/-- The functor `K ↦ RΓ(U, Lf^* K)` from `D_QCoh(𝒪_X)` to `D(A)`. -/
noncomputable def pullbackFunctor {A : Type u} [CommRing A]
    {X U : AlgebraicSpace (Spec (CommRingCat.of A))} (f : U ⟶ X) :
    DerivedQCoh X ⥤ DerivedCategory (ModuleCat.{u} A) :=
  DerivedQCoh.inclusion X ⋙ ModuleDerived.pullback f ⋙
    globalSectionsOver (SchemeRealization.toBase U)

/-- Evaluating `pullbackFunctor f` is derived pullback along `f` followed by derived
global sections of `U` over `A`. -/
theorem pullbackFunctor_obj {A : Type u} [CommRing A]
    {X U : AlgebraicSpace (Spec (CommRingCat.of A))} (f : U ⟶ X)
    (K : DerivedQCoh X) :
    (pullbackFunctor f).obj K =
      (globalSectionsOver (SchemeRealization.toBase U)).obj ((ModuleDerived.pullback f).obj K.obj) :=
  sorry

/-- The sequential functor diagram whose `n`th term is global sections over `A`
of the internal Hom from `Lₙ` to `K` in the selected closed model `H`. -/
noncomputable def rHomDiagram {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X))
    (L : ℕᵒᵖ ⥤ ModuleDerived X) :
    ℕ ⥤ (DerivedQCoh X ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  L.rightOp ⋙ internalHomOf H ⋙
    (whiskeringRight (ModuleDerived X) (ModuleDerived X)
        (DerivedCategory (ModuleCat.{u} A))).obj
      (globalSectionsOver (SchemeRealization.toBase X)) ⋙
    (whiskeringLeft (DerivedQCoh X) (ModuleDerived X)
        (DerivedCategory (ModuleCat.{u} A))).obj
      (DerivedQCoh.inclusion X)

/-- Evaluating `rHomDiagram H L` at `n` and `K` gives derived global sections of the
internal Hom in the selected closed model `H` from `Lₙ` to the underlying derived
module of `K`. -/
theorem rHomDiagram_obj_obj {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X))
    (L : ℕᵒᵖ ⥤ ModuleDerived X) (n : ℕ) (K : DerivedQCoh X) :
    ((rHomDiagram H L).obj n).obj K =
      (globalSectionsOver (SchemeRealization.toBase X)).obj
        ((ihomOf H (L.obj (Opposite.op n))).obj K.obj) :=
  sorry

/-- The sequential functor diagram whose `n`th term sends `K` to
`RΓ(X, Eₙ ⊗ᴸ K)`, regarded in `D(A)`. -/
noncomputable def tensorDiagram {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (E : ℕ ⥤ ModuleDerived X) :
    ℕ ⥤ (DerivedQCoh X ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  E ⋙ curry.obj
      (DerivedTensor.Bifunctor.functor :
        ModuleDerived X × ModuleDerived X ⥤ ModuleDerived X) ⋙
    (whiskeringRight (ModuleDerived X) (ModuleDerived X)
        (DerivedCategory (ModuleCat.{u} A))).obj
      (globalSectionsOver (SchemeRealization.toBase X)) ⋙
    (whiskeringLeft (DerivedQCoh X) (ModuleDerived X)
        (DerivedCategory (ModuleCat.{u} A))).obj
      (DerivedQCoh.inclusion X)

/-- Evaluating `tensorDiagram E` at `n` and `K` gives derived global sections of
`Eₙ ⊗ᴸ K`. -/
theorem tensorDiagram_obj_obj {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (E : ℕ ⥤ ModuleDerived X) (n : ℕ) (K : DerivedQCoh X) :
    ((tensorDiagram E).obj n).obj K =
      (globalSectionsOver (SchemeRealization.toBase X)).obj
        (DerivedTensor.Bifunctor.obj (E.obj n) K.obj) :=
  sorry

/-- For a flat morphism `f : U ⟶ X` of algebraic spaces of finite presentation over
`A`, there is an inverse system `L : ℕᵒᵖ ⥤ D(𝒪_X)` of perfect objects such that
`K ↦ RΓ(U, Lf^* K)` is functorially its sequential `RHom` homotopy-colimit
presentation in `D(A)`, for a closed model whose braided tensor is specified by
the derived structure-ring tensor universal property. -/
theorem exists_perfect_rHom {A : Type u} [CommRing A]
    {X U : AlgebraicSpace (Spec (CommRingCat.of A))} (f : U ⟶ X)
    [FinitePresentation (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase U)] [Flat f]
    [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
    (H : MonoidalClosed (ModuleDerived X))
    (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := Modules X)) :
    ∃ L : ℕᵒᵖ ⥤ ModuleDerived X,
      (∀ n : ℕ, ModuleDerived.IsPerfect (L.obj (Opposite.op n))) ∧
        Functorial.IsOf (rHomDiagram H L) (pullbackFunctor f) :=
  sorry

/-- For a flat morphism `f : U ⟶ X` of algebraic spaces of finite presentation over
`A`, there is a direct system `E : ℕ ⥤ D(𝒪_X)` of perfect objects such that
`K ↦ RΓ(U, Lf^* K)` is functorially the sequential homotopy colimit of
`K ↦ RΓ(X, Eₙ ⊗ᴸ K)` in `D(A)`. -/
theorem exists_perfect_tensor {A : Type u} [CommRing A]
    {X U : AlgebraicSpace (Spec (CommRingCat.of A))} (f : U ⟶ X)
    [FinitePresentation (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase U)] [Flat f] :
    ∃ E : ℕ ⥤ ModuleDerived X,
      (∀ n : ℕ, ModuleDerived.IsPerfect (E.obj n)) ∧
        Functorial.IsOf (tensorDiagram E) (pullbackFunctor f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FlatPullbackSections
