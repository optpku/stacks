module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Functorial
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_20_1_ProjectionFormula
public import stacks_project.Chap75.Lemma_75_25_7_GlobalSections
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

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
  DerivedQCoh.inclusion X ⋙ modulePullbackDerived f ⋙
    globalSectionsOver (toBase U)

/-- Evaluating `pullbackFunctor f` is derived pullback along `f` followed by derived
global sections of `U` over `A`. -/
theorem pullbackFunctor_obj {A : Type u} [CommRing A]
    {X U : AlgebraicSpace (Spec (CommRingCat.of A))} (f : U ⟶ X)
    (K : DerivedQCoh X) :
    (pullbackFunctor f).obj K =
      (globalSectionsOver (toBase U)).obj ((modulePullbackDerived f).obj K.obj) :=
  sorry

/-- The sequential functor diagram whose `n`th term sends `K` to
`RΓ(X, RHom(Lₙ, K))`, regarded in `D(A)`. -/
noncomputable def rHomDiagram {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X))
    (L : ℕᵒᵖ ⥤ ModuleDerived X) :
    ℕ ⥤ (DerivedQCoh X ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  L.rightOp ⋙ internalHomOf H ⋙
    (whiskeringRight (ModuleDerived X) (ModuleDerived X)
        (DerivedCategory (ModuleCat.{u} A))).obj
      (globalSectionsOver (toBase X)) ⋙
    (whiskeringLeft (DerivedQCoh X) (ModuleDerived X)
        (DerivedCategory (ModuleCat.{u} A))).obj
      (DerivedQCoh.inclusion X)

/-- Evaluating `rHomDiagram H L` at `n` and `K` gives derived global sections of the
internal Hom from `Lₙ` to the underlying derived module of `K`. -/
theorem rHomDiagram_obj_obj {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X))
    (L : ℕᵒᵖ ⥤ ModuleDerived X) (n : ℕ) (K : DerivedQCoh X) :
    ((rHomDiagram H L).obj n).obj K =
      (globalSectionsOver (toBase X)).obj
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
      (globalSectionsOver (toBase X)) ⋙
    (whiskeringLeft (DerivedQCoh X) (ModuleDerived X)
        (DerivedCategory (ModuleCat.{u} A))).obj
      (DerivedQCoh.inclusion X)

/-- Evaluating `tensorDiagram E` at `n` and `K` gives derived global sections of
`Eₙ ⊗ᴸ K`. -/
theorem tensorDiagram_obj_obj {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    (E : ℕ ⥤ ModuleDerived X) (n : ℕ) (K : DerivedQCoh X) :
    ((tensorDiagram E).obj n).obj K =
      (globalSectionsOver (toBase X)).obj
        (DerivedTensor.Bifunctor.obj (E.obj n) K.obj) :=
  sorry

/-- For a flat morphism `f : U ⟶ X` of algebraic spaces of finite presentation over
`A`, there is an inverse system `L : ℕᵒᵖ ⥤ D(𝒪_X)` of perfect objects such that
`K ↦ RΓ(U, Lf^* K)` is functorially its sequential `RHom` homotopy-colimit
presentation in `D(A)`. -/
theorem exists_perfect_rHom {A : Type u} [CommRing A]
    {X U : AlgebraicSpace (Spec (CommRingCat.of A))} (f : U ⟶ X)
    [FinitePresentation (toBase X)] [FinitePresentation (toBase U)] [Flat f]
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X)) :
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
    [FinitePresentation (toBase X)] [FinitePresentation (toBase U)] [Flat f] :
    ∃ E : ℕ ⥤ ModuleDerived X,
      (∀ n : ℕ, ModuleDerived.IsPerfect (E.obj n)) ∧
        Functorial.IsOf (tensorDiagram E) (pullbackFunctor f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FlatPullbackSections
