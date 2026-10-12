/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.BoundedAbove
import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.BoundedAbove.R1
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Above Limits of Derived Module Towers

For a Cartesian tower over surjective ring transitions, epimorphy on top cohomology removes the
extra `R¹lim` degree from the coarse homotopy-limit bound.  Nilpotent transition kernels are used
only to propagate a fixed upper bound through an `AllOrTail` hypothesis.
@stack 09AU
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Filter

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedTower

variable {A : SequentialInverseSystem CommRingCat.{u}}

/-- Across a surjective transition with nilpotent kernel, a Cartesian comparison reflects and
preserves a fixed upper cohomological bound. -/
@[stacks 09AU "upper-bound propagation across a nilpotent transition"]
theorem IsCartesian.isLE_succ_iff {T : DerivedTower A}
    (h_cartesian : T.IsCartesian) (n : ℕ)
    (h_surjective : Function.Surjective (A.stepMap n).hom)
    (h_nilpotent : IsNilpotent (RingHom.ker (A.stepMap n).hom)) (b : ℤ) :
    (T.obj (n + 1)).IsLE b ↔ (T.obj n).IsLE b := sorry

/-- For a Cartesian tower over a surjective ring transition, the fixed-base transition is
epimorphic on top cohomology once the successor stage has the corresponding upper bound. -/
@[stacks 09AU "epimorphic top cohomology transition in a Cartesian tower"]
theorem IsCartesian.epi_homology_restrictStep {T : DerivedTower A}
    (h_cartesian : T.IsCartesian) (s : Cone A) (n : ℕ)
    (h_surjective : Function.Surjective (A.stepMap n).hom) (b : ℤ)
    (h_bound : (T.obj (n + 1)).IsLE b) :
    Epi ((DerivedCategory.homologyFunctor
      (ModuleCat.{u, u} (s.pt : Type u)) b).map (T.restrictStep s n)) := sorry

namespace BoundedAbove

/-- A fixed upper bound in the all-stages-or-nilpotent-tail form eventually holds throughout a
Cartesian tower over surjective transitions. -/
theorem eventually (T : DerivedTower A) {b : ℤ}
    (h_surjective : A.Surjective)
    (h_bound : A.AllOrTail (fun n ↦ (T.obj n).IsLE b))
    (h_cartesian : T.IsCartesian) :
    ∀ᶠ n in atTop, (T.obj n).IsLE b := sorry

/-- An eventual uniform upper bound is preserved exactly by a homotopy limit of a Cartesian
tower over surjective ring transitions. -/
theorem of_eventually (T : DerivedTower A) (s : Cone A) {b : ℤ}
    (h_surjective : A.Surjective) (h_cartesian : T.IsCartesian)
    (h_bound : ∀ᶠ n in atTop, (T.obj n).IsLE b)
    {K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))}
    (hK : HomotopyLimit.IsOf (T.restrict s) K) :
    K.IsLE b := sorry

/-- A homotopy limit preserves a fixed upper bound supplied in the
all-stages-or-nilpotent-tail form. -/
@[stacks 09AU "sharp upper bound for a derived module tower limit"]
theorem limit_isLE (T : DerivedTower A) (s : Cone A) {b : ℤ}
    (h_surjective : A.Surjective)
    (h_bound : A.AllOrTail (fun n ↦ (T.obj n).IsLE b))
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))}
    (hK : HomotopyLimit.IsOf (T.restrict s) K) :
    K.IsLE b := sorry

/-- A homotopy limit is bounded above when some upper bound satisfies the
all-stages-or-nilpotent-tail condition. -/
@[stacks 09AU "bounded-above derived module tower limit"]
theorem limit (T : DerivedTower A) (s : Cone A)
    (h_surjective : A.Surjective)
    (h_bound : ∃ b : ℤ, A.AllOrTail (fun n ↦ (T.obj n).IsLE b))
    (h_cartesian : T.IsCartesian)
    {K : DerivedCategory (ModuleCat.{u, u} (s.pt : Type u))}
    (hK : HomotopyLimit.IsOf (T.restrict s) K) :
    K.IsBoundedAbove := sorry

end BoundedAbove

end CategoryTheory.ModuleCat.DerivedTower
