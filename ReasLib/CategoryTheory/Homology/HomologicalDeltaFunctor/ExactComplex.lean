module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homological delta functors from exact chain-complex functors

An exact additive functor into nonnegatively indexed chain complexes has a canonical homological
delta functor.  This is the lower-indexed counterpart of
`CohomologicalDeltaFunctor.ExactComplex`.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.ComposableArrows

noncomputable section

universe vA vB uA uB

namespace CategoryTheory.HomologicalDeltaFunctor.ExactComplex

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (K : A ⥤ ChainComplex B ℕ) [K.Additive]

/-- The additive degree-`n` homology functor of an exact chain-complex functor. -/
@[stacks 010Q "degree of an exact chain-complex functor"]
noncomputable abbrev degree (n : ℕ) : A ⥤+ B :=
  AdditiveFunctor.of
    (K ⋙ HomologicalComplex.homologyFunctor B (ComplexShape.down ℕ) n)

/-- An exact chain-complex functor sends a short exact sequence to a short exact sequence of
complexes. -/
@[stacks 010Q "short-exact image of an exact chain-complex functor"]
theorem map_shortExact [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    {S : ShortComplex A} (hS : S.ShortExact) :
    (S.map K).ShortExact := sorry

/-- Exactness-property bridge for callers that already package both preservation facts. -/
@[stacks 010Q "exactness bridge for chain-complex functors"]
theorem map_shortExact_of_exact (hK : exactFunctor A (ChainComplex B ℕ) K)
    {S : ShortComplex A} (hS : S.ShortExact) :
    (S.map K).ShortExact := sorry

/-- The connecting morphism in homology of the image of a short exact sequence. -/
@[stacks 010Q "connecting morphism of an exact chain-complex functor"]
noncomputable def connecting [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ((degree K (n + 1)).obj).obj S.X₃ ⟶ ((degree K n).obj).obj S.X₁ :=
  (map_shortExact K hS).δ (n + 1) n
    (ComplexShape.down_mk (n + 1) n rfl)

/-- The degree-zero image of the quotient map of a short exact sequence is epic. -/
@[stacks 010Q "epimorphism in degree zero homology"]
theorem epi_map_g_zero [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    {S : ShortComplex A} (hS : S.ShortExact) :
    Epi ((degree K 0).obj.map S.g) := sorry

/-- The degree-zero homology branch of an exact nonnegative chain-complex functor is right
exact. -/
@[stacks 010Q "right exactness of degree-zero homology"]
theorem degree_zero_preservesFiniteColimits [PreservesFiniteLimits K]
    [PreservesFiniteColimits K] :
    PreservesFiniteColimits (degree K 0).obj := sorry

/-- The five-arrow homology window of an exact chain-complex functor is exact. -/
@[stacks 010Q "long exact homology window"]
theorem exact₅ [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (mk₅ ((degree K (n + 1)).obj.map S.f) ((degree K (n + 1)).obj.map S.g)
      (connecting K hS n) ((degree K n).obj.map S.f)
      ((degree K n).obj.map S.g)).Exact := sorry

/-- The homology connecting morphisms are natural in morphisms of short exact sequences. -/
@[stacks 010Q "naturality of homology connecting morphisms"]
theorem connecting_naturality [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    {S T : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (n : ℕ) :
    CommSq ((degree K (n + 1)).obj.map f.τ₃) (connecting K hS n)
      (connecting K hT n) ((degree K n).obj.map f.τ₁) := sorry

/-- The homological delta functor canonically attached to an exact additive functor into
nonnegative chain complexes. -/
@[stacks 010Q "delta functor of an exact chain-complex functor"]
noncomputable def functor
    (K : A ⥤ ChainComplex B ℕ) [K.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K] :
    HomologicalDeltaFunctor A B where
  F := degree K
  δ := fun {S} hS n ↦ connecting K (S := S) hS n
  epi_map_g_zero := fun {S} hS ↦ epi_map_g_zero K (S := S) hS
  exact₅ := fun {S} hS n ↦ exact₅ K (S := S) hS n
  δ_naturality := fun {S T} hS hT f n ↦
    connecting_naturality K (S := S) (T := T) hS hT f n

/-- The homological delta functor attached to a bundled exact functor.  The preservation fields
are read directly from the bundle, so callers do not need temporary typeclass bindings. -/
@[stacks 010Q "delta functor from a bundled exact functor"]
noncomputable def functorBundled
    (K : ExactFunctor A (ChainComplex B ℕ)) :
    HomologicalDeltaFunctor A B :=
  @functor A _ _ B _ _ K.1 inferInstance K.2.1 K.2.2

/-- The homological delta functor attached to an ordinary exact functor together with its exactness
proof. -/
@[stacks 010Q "delta functor from an exactness proof"]
noncomputable def functorOfExact
    (K : CategoryTheory.Functor A (ChainComplex B ℕ))
    (hK : exactFunctor A (ChainComplex B ℕ) K) :
    HomologicalDeltaFunctor A B :=
  functorBundled ⟨K, hK⟩

/-- The degree branches of the delta functor attached to a bundled exact functor. -/
@[simp, stacks 010Q "degree formula for a bundled exact chain-complex functor"]
theorem functorBundled_obj
    (K : ExactFunctor A (ChainComplex B ℕ)) (n : ℕ) :
    ((functorBundled K n).obj) = K.1 ⋙
      HomologicalComplex.homologyFunctor B (ComplexShape.down ℕ) n := sorry

/-- The connecting morphism attached to a bundled exact functor. -/
@[simp, stacks 010Q "connecting formula for a bundled exact chain-complex functor"]
theorem functorBundled_δ
    (K : ExactFunctor A (ChainComplex B ℕ))
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (functorBundled K).δ hS n = connecting K.1 hS n := sorry

/-- The degree branches of `functor K` are the homology functors of `K`. -/
@[simp, stacks 010Q "degree formula for the homological delta functor"]
theorem functor_obj [PreservesFiniteLimits K] [PreservesFiniteColimits K] (n : ℕ) :
    ((functor K n).obj) = K ⋙
      HomologicalComplex.homologyFunctor B (ComplexShape.down ℕ) n := sorry

/-- The connecting morphism of `functor K` is the boundary map of the mapped short exact
sequence. -/
@[simp, stacks 010Q "connecting formula for the homological delta functor"]
theorem functor_δ [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (functor K).δ hS n = connecting K hS n := sorry

end CategoryTheory.HomologicalDeltaFunctor.ExactComplex
