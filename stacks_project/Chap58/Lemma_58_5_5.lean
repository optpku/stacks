module

public import stacks_project.Chap58.Lemma_58_5_5_Fiber
public import Mathlib.CategoryTheory.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Galois
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

universe u

/-- The finite étale category over a connected scheme satisfies the categorical
axioms of a pre-Galois category. -/
abbrev finiteEtale_preGaloisCategory {X : Scheme.{u}} [ConnectedSpace X] :
    PreGaloisCategory (Scheme.FiniteEtale X) := Scheme.FiniteEtale.preGaloisCategory

/-- The explicit geometric-fiber functor at a geometric point is a fiber functor. -/
noncomputable abbrev finiteEtaleFiber_isFiberFunctor {X : Scheme.{u}}
    [ConnectedSpace X] (xbar : Scheme.GeometricPoint X) :
    FiberFunctor (xbar.finiteEtaleFiber (fun Y ↦
      Scheme.GeometricPoint.finiteEtaleFiberObj_finite xbar Y)) :=
  @Scheme.FiniteEtale.finiteFiber_isFiberFunctor X _ xbar.K xbar.field
    xbar.isAlgClosed xbar.hom

/-- A connected scheme admitting a geometric point has a Galois finite étale category. -/
abbrev finiteEtale_galoisCategory_of_nonempty {X : Scheme.{u}} [ConnectedSpace X]
    [Nonempty (Scheme.GeometricPoint X)] :
    GaloisCategory (Scheme.FiniteEtale X) := Scheme.FiniteEtale.galoisCategory

/-- For a connected scheme `X` and a geometric point `xbar`,
the finite étale category `Scheme.FiniteEtale X` is a Galois category via
the geometric-fiber functor at `xbar`. -/
abbrev finiteEtale_galoisCategory {X : Scheme.{u}} [ConnectedSpace X]
    (xbar : Scheme.GeometricPoint X) :
    GaloisCategory (Scheme.FiniteEtale X) := Scheme.FiniteEtale.galoisCategory

/- Lemma 58.5.5: the specified geometric-fiber functor over a connected scheme
defines a Galois category. -/
@[stacks 0BNB] #check (AlgebraicGeometry.Scheme.FiniteEtale.fiber_isGalois :
  ∀ {X : Scheme.{u}} [ConnectedSpace X] {K : Type u} [Field K] [IsAlgClosed K]
    (point : Spec (.of K) ⟶ X),
    CategoryTheory.Functor.IsGalois (AlgebraicGeometry.Scheme.FiniteEtale.fiber point))
