module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Comparison.At
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial base change for canonical module RHom

This leaf owns the two-variable comparison
`E(RHom_A(K, L)) ⟶ RHom_B(E(K), E(L))`.  Its inputs expose the two independent coherence
requirements: a natural tensor comparison for `E`, and coherent bifunctor comparisons between
canonical `RHom` and selected internal Homs on both sides.  Objectwise model isomorphisms alone do
not suffice to define this natural transformation.

The module facade is same-universe, matching the current standard-universe canonical `RHom`
convenience API.  The underlying categorical owner in `PullbackComparison.Natural` is fully
universe-polymorphic.  Its ordinary comparison path uses the left-ordered, braiding-free
transpose; source-order consumers can still import the generic `Bifunctor` owner explicitly.

@stack 08I4
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- 08I4: The source bifunctor for canonical `RHom` base change along `E`. -/
@[stacks 08I4 "canonical RHom base-change source bifunctor"]
noncomputable abbrev sourceFunctor
    (E : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B))
    [RHom.Has (A := A)] :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ ×
        DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B) :=
  RHom.BaseChange.At.sourceFunctor E

/-- 08I4: The target bifunctor for canonical `RHom` base change along `E`. -/
@[stacks 08I4 "canonical RHom base-change target bifunctor"]
noncomputable abbrev targetFunctor
    (E : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B))
    [RHom.Has (A := B)] :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ ×
        DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B) :=
  RHom.BaseChange.At.targetFunctor E

section Comparison

variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
variable [RHom.Has (A := A)] [RHom.Has (A := B)]

/-- 08I4: A component of the canonical `RHom` base-change comparison. -/
@[stacks 08I4 "canonical RHom base-change component"]
noncomputable abbrev comparisonApp
    (E : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B))
    (M : RHom.BifunctorComparison (A := A))
    (M' : RHom.BifunctorComparison (A := B))
    (T : Functor.TensorComparison E)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (sourceFunctor E).obj (Opposite.op K, L) ⟶
      (targetFunctor E).obj (Opposite.op K, L) :=
  RHom.BaseChange.At.comparisonApp E M M' T K L

/-- 08I4: Naturality of the canonical `RHom` base-change components in both variables. -/
@[stacks 08I4 "canonical RHom base-change naturality"]
theorem comparisonApp_naturality
    (E : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B))
    (M : RHom.BifunctorComparison (A := A))
    (M' : RHom.BifunctorComparison (A := B))
    (T : Functor.TensorComparison E)
    {P Q : (DerivedCategory (ModuleCat.{u} A))ᵒᵖ ×
      DerivedCategory (ModuleCat.{u} A)} (f : P ⟶ Q) :
    (sourceFunctor E).map f ≫
        comparisonApp E M M' T Q.1.unop Q.2 =
      comparisonApp E M M' T P.1.unop P.2 ≫
        (targetFunctor E).map f :=
  RHom.BaseChange.At.comparisonApp_naturality E M M' T f

/-- 08I4: The two-variable canonical `RHom` base-change comparison. -/
@[stacks 08I4 "canonical RHom base-change natural transformation"]
noncomputable abbrev comparison
    (E : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B))
    (M : RHom.BifunctorComparison (A := A))
    (M' : RHom.BifunctorComparison (A := B))
    (T : Functor.TensorComparison E) :
    sourceFunctor E ⟶ targetFunctor E :=
  RHom.BaseChange.At.comparison E M M' T

/-- 08I4: A component of the natural transformation is the explicit three-step comparison map. -/
@[simp, stacks 08I4 "canonical RHom base-change natural transformation component"]
theorem comparison_app
    (E : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B))
    (M : RHom.BifunctorComparison (A := A))
    (M' : RHom.BifunctorComparison (A := B))
    (T : Functor.TensorComparison E)
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (comparison E M M' T).app (Opposite.op K, L) =
      comparisonApp E M M' T K L :=
  RHom.BaseChange.At.comparison_app E M M' T K L

/-- Contravariant source naturality of canonical `RHom` base change. -/
@[reassoc, stacks 08I4 "canonical RHom base-change source naturality"]
theorem comparison_natural_source
    (E : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B))
    (M : RHom.BifunctorComparison (A := A))
    (M' : RHom.BifunctorComparison (A := B))
    (T : Functor.TensorComparison E)
    {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)} (f : K₂ ⟶ K₁)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    E.map (RHom.map (A := A) f (𝟙 L)) ≫ comparisonApp E M M' T K₂ L =
      comparisonApp E M M' T K₁ L ≫
        RHom.map (A := B) (E.map f) (𝟙 (E.obj L)) :=
  RHom.BaseChange.At.comparison_natural_source E M M' T f L

/-- Covariant target naturality of canonical `RHom` base change. -/
@[reassoc, stacks 08I4 "canonical RHom base-change target naturality"]
theorem comparison_natural_target
    (E : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} B))
    (M : RHom.BifunctorComparison (A := A))
    (M' : RHom.BifunctorComparison (A := B))
    (T : Functor.TensorComparison E)
    (K : DerivedCategory (ModuleCat.{u} A))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} A)} (f : L₁ ⟶ L₂) :
    E.map (RHom.map (A := A) (𝟙 K) f) ≫ comparisonApp E M M' T K L₂ =
      comparisonApp E M M' T K L₁ ≫
        RHom.map (A := B) (𝟙 (E.obj K)) (E.map f) :=
  RHom.BaseChange.At.comparison_natural_target E M M' T K f

end Comparison

end CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange
