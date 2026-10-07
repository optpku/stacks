module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor

/-!
# Scalar extension of finite free complexes

This file keeps the chosen finite-free coordinates while extending scalars.
The construction is deliberately owned by `FiniteFreeComplex`, rather than by
an application-specific fiber construction.

@stack 00MS
-/

@[expose] public section

universe u v

open CategoryTheory ChainComplex
open scoped TensorProduct

section

variable {R : Type u} [CommRing R]
variable {e : ℕ}

namespace FiniteFreeComplex

/-- The underlying chain complex obtained by applying categorical extension of scalars to `C`.

The target module category is written at the common carrier universe `max u v` required by the
current `FiniteFreeComplex` owner, whose module-category carrier universe is tied to its ring
universe. `ModuleCat.extendScalars` supplies this target level. -/
@[stacks 00MS "finite free base change"]
noncomputable def baseChangeComplex (C : _root_.FiniteFreeComplex R e)
    (S : Type (max u v)) [CommRing S] [Algebra R S] :
    ChainComplex (ModuleCat.{max u v} S) ℕ :=
  ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    C.toChainComplex

namespace baseChangeComplex

/-- The scalar-extended complex is zero in every degree strictly above the bound of `C`. -/
@[stacks 00MS "finite free base change"]
theorem isZero_X (C : _root_.FiniteFreeComplex R e)
    (S : Type (max u v)) [CommRing S] [Algebra R S] (i : ℕ) (hi : e < i) :
    Limits.IsZero ((C.baseChangeComplex S).X i) := sorry

/-- The scalar extension of a chosen coordinate identification to a finite free `S`-module.
This is exposed separately so matrix and rank arguments can use the coordinates induced by the
chosen `C.termIso` data, without rebuilding a local equivalence. -/
@[stacks 00MS "finite free base change coordinates"]
noncomputable def termIso (C : _root_.FiniteFreeComplex R e)
    (S : Type (max u v)) [CommRing S] [Algebra R S] (i : Fin (e + 1)) :
    (C.baseChangeComplex S).X i ≅
      ModuleCat.of S (Fin (C.rank i) → S) :=
  ModuleCat.ExtendScalars.tensorIso (R := R) (S := S) (C.toChainComplex.X i) ≪≫
    (LinearEquiv.baseChange R S (C.toChainComplex.X i) (Fin (C.rank i) → R)
      (C.termIso i).toLinearEquiv).toModuleIso ≪≫
    (TensorProduct.piScalarRight R S S (Fin (C.rank i))).toModuleIso

end baseChangeComplex

/-- The bounded finite free complex obtained from `C` by extending scalars from `R` to `S`.
Its terms retain the canonical finite free coordinates induced by those of `C`. -/
@[stacks 00MS "finite free base change"]
noncomputable def baseChange (C : _root_.FiniteFreeComplex R e) (S : Type (max u v)) [CommRing S]
    [Algebra R S] : _root_.FiniteFreeComplex S e where
  toChainComplex := C.baseChangeComplex S
  isZero_toChainComplex_X i hi := baseChangeComplex.isZero_X C S i hi
  rank := C.rank
  termIso i := baseChangeComplex.termIso C S i

namespace baseChange

/-- Forgetting the chosen coordinates from `baseChange` recovers the canonical scalar-extended
chain complex. -/
@[simp, stacks 00MS "finite free base change"]
theorem toChainComplex (C : _root_.FiniteFreeComplex R e) (S : Type (max u v))
    [CommRing S] [Algebra R S] :
    (C.baseChange S).toChainComplex = C.baseChangeComplex S := sorry

/-- Scalar extension preserves each selected finite-free rank. -/
@[simp, stacks 00MS "finite free base change"]
theorem rank_apply (C : _root_.FiniteFreeComplex R e) (S : Type (max u v))
    [CommRing S] [Algebra R S] (i : Fin (e + 1)) :
    (C.baseChange S).rank i = C.rank i := sorry

end baseChange

end FiniteFreeComplex

end
