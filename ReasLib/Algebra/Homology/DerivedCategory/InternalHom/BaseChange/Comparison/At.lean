/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor.At
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Carrier-polymorphic base change for canonical module RHom

This leaf owns the natural transformation
`E(RHom_R(K, L)) ⟶ RHom_S(E(K), E(L))` with independent ring and module-carrier universes.
It consumes an honest tensor-bifunctor comparison for `E` and coherent two-variable comparisons
on both sides.  It neither installs a local monoidal instance nor derives naturality from an
objectwise family.

The component uses the left-ordered internal-Hom transpose, so ordinary base change needs only
the two ambient monoidal structures; the source-order braided view remains available separately.

@stack 08I4
-/

@[expose] public section

noncomputable section

universe r v s w

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.At

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S]

/-- 08I4: The carrier-polymorphic source bifunctor for canonical `RHom` base change along `E`. -/
@[stacks 08I4 "carrier-polymorphic canonical RHom base-change source bifunctor"]
noncomputable abbrev sourceFunctor
    (E : RHom.At.Derived.{r, v} (R := R) ⥤ RHom.At.Derived.{s, w} (R := S))
    [RHom.At.Has.{r, v} (R := R)] :
    (RHom.At.Derived.{r, v} (R := R))ᵒᵖ × RHom.At.Derived.{r, v} (R := R) ⥤
      RHom.At.Derived.{s, w} (R := S) :=
  RHom.At.functor (R := R) ⋙ E

/-- 08I4: The carrier-polymorphic target bifunctor for canonical `RHom` base change along `E`. -/
@[stacks 08I4 "carrier-polymorphic canonical RHom base-change target bifunctor"]
noncomputable abbrev targetFunctor
    (E : RHom.At.Derived.{r, v} (R := R) ⥤ RHom.At.Derived.{s, w} (R := S))
    [RHom.At.Has.{s, w} (R := S)] :
    (RHom.At.Derived.{r, v} (R := R))ᵒᵖ × RHom.At.Derived.{r, v} (R := R) ⥤
      RHom.At.Derived.{s, w} (R := S) :=
  Functor.prod E.op E ⋙ RHom.At.functor (R := S)

section Comparison

variable [MonoidalCategory (RHom.At.Derived.{r, v} (R := R))]
variable [MonoidalCategory (RHom.At.Derived.{s, w} (R := S))]
variable [RHom.At.Has.{r, v} (R := R)] [RHom.At.Has.{s, w} (R := S)]

/-- 08I4: A component of the carrier-polymorphic canonical `RHom` base-change comparison. -/
@[stacks 08I4 "carrier-polymorphic canonical RHom base-change component"]
noncomputable def comparisonApp
    (E : RHom.At.Derived.{r, v} (R := R) ⥤ RHom.At.Derived.{s, w} (R := S))
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : Functor.TensorComparison E)
    (K L : RHom.At.Derived.{r, v} (R := R)) :
    (sourceFunctor E).obj (Opposite.op K, L) ⟶
      (targetFunctor E).obj (Opposite.op K, L) :=
  E.map (M.objIso K L).hom ≫
    Functor.PullbackInternalHom.Left.comparisonApp
      M.closed M'.closed E T K L ≫
    (M'.objIso (E.obj K) (E.obj L)).inv

/-- 08I4: The two-variable carrier-polymorphic canonical `RHom` base-change comparison, assembled
as a composite of three natural transformations. -/
@[stacks 08I4 "carrier-polymorphic canonical RHom base-change natural transformation"]
noncomputable def comparison
    (E : RHom.At.Derived.{r, v} (R := R) ⥤ RHom.At.Derived.{s, w} (R := S))
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : Functor.TensorComparison E) :
    sourceFunctor E ⟶ targetFunctor E :=
  Functor.whiskerRight M.functorIso.hom E ≫
    Functor.PullbackInternalHom.Left.comparison M.closed M'.closed E T ≫
    Functor.whiskerLeft (Functor.prod E.op E) M'.functorIso.inv

/-- 08I4: Naturality of the carrier-polymorphic base-change components in both variables. -/
@[stacks 08I4 "carrier-polymorphic canonical RHom base-change naturality"]
theorem comparisonApp_naturality
    (E : RHom.At.Derived.{r, v} (R := R) ⥤ RHom.At.Derived.{s, w} (R := S))
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : Functor.TensorComparison E)
    {P Q : (RHom.At.Derived.{r, v} (R := R))ᵒᵖ ×
      RHom.At.Derived.{r, v} (R := R)} (f : P ⟶ Q) :
    (sourceFunctor E).map f ≫ comparisonApp E M M' T Q.1.unop Q.2 =
      comparisonApp E M M' T P.1.unop P.2 ≫ (targetFunctor E).map f := by
  exact (comparison E M M' T).naturality f

/-- 08I4: A component of the carrier-polymorphic natural transformation is its explicit
three-step comparison map. -/
@[simp, stacks 08I4 "carrier-polymorphic canonical RHom base-change transformation component"]
theorem comparison_app
    (E : RHom.At.Derived.{r, v} (R := R) ⥤ RHom.At.Derived.{s, w} (R := S))
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : Functor.TensorComparison E)
    (K L : RHom.At.Derived.{r, v} (R := R)) :
    (comparison E M M' T).app (Opposite.op K, L) = comparisonApp E M M' T K L := rfl

/-- 08I4: Contravariant source naturality of carrier-polymorphic canonical `RHom` base change. -/
@[reassoc, stacks 08I4 "carrier-polymorphic canonical RHom base-change source naturality"]
theorem comparison_natural_source
    (E : RHom.At.Derived.{r, v} (R := R) ⥤ RHom.At.Derived.{s, w} (R := S))
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : Functor.TensorComparison E)
    {K₁ K₂ : RHom.At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁)
    (L : RHom.At.Derived.{r, v} (R := R)) :
    E.map (RHom.At.map (R := R) f (𝟙 L)) ≫ comparisonApp E M M' T K₂ L =
      comparisonApp E M M' T K₁ L ≫
        RHom.At.map (R := S) (E.map f) (𝟙 (E.obj L)) := by
  simpa only [sourceFunctor, targetFunctor, Functor.comp_map,
    RHom.At.functor, RHom.At.map, Functor.prod_map, Functor.op_map,
    Functor.map_id, op_id] using!
    comparisonApp_naturality E M M' T
      ((f.op, 𝟙 L) : (Opposite.op K₁, L) ⟶ (Opposite.op K₂, L))

/-- 08I4: Covariant target naturality of carrier-polymorphic canonical `RHom` base change. -/
@[reassoc, stacks 08I4 "carrier-polymorphic canonical RHom base-change target naturality"]
theorem comparison_natural_target
    (E : RHom.At.Derived.{r, v} (R := R) ⥤ RHom.At.Derived.{s, w} (R := S))
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : Functor.TensorComparison E)
    (K : RHom.At.Derived.{r, v} (R := R))
    {L₁ L₂ : RHom.At.Derived.{r, v} (R := R)} (f : L₁ ⟶ L₂) :
    E.map (RHom.At.map (R := R) (𝟙 K) f) ≫ comparisonApp E M M' T K L₂ =
      comparisonApp E M M' T K L₁ ≫
        RHom.At.map (R := S) (𝟙 (E.obj K)) (E.map f) := by
  simpa only [sourceFunctor, targetFunctor, Functor.comp_map,
    RHom.At.functor, RHom.At.map, Functor.prod_map, Functor.op_map,
    Functor.map_id, op_id, unop_id] using!
    comparisonApp_naturality E M M' T
      ((𝟙 (Opposite.op K), f) : (Opposite.op K, L₁) ⟶ (Opposite.op K, L₂))

end Comparison

end CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.At
