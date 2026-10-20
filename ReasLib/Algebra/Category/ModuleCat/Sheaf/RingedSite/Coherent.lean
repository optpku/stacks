module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalGeneration
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherent Sheaves of Modules on a Site

Coherence is expressed using Mathlib's finite-type owner and kernels of maps
from finite free sheaves on slices.  The definition is independent of
commutativity of the structure sheaf.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A sheaf of modules is coherent when it is of finite type and the kernel of every map from a
finite free sheaf on every slice is of finite type. -/
@[stacks 03DL "(8)", stacks 01BV "ringed-space specialization"]
class IsCoherent (M : SheafOfModules.{w} R) : Prop extends M.IsFiniteType where
  /-- Kernels of maps from finite free sheaves on slices are of finite type. -/
  relationKernelFiniteType (U : C) (r : ℕ)
      (φ :
        (SheafOfModules.free (R := R.over U) (ULift.{w} (Fin r)) :
          SheafOfModules.{w} (R.over U)) ⟶ M.over U) :
      (kernel φ).IsFiniteType

variable (R) in
/-- The object property of coherent sheaves of modules over `R`. -/
@[stacks 01BV "coherent module property"]
abbrev isCoherent : ObjectProperty (SheafOfModules.{w} R) :=
  IsCoherent

namespace IsCoherent

/-- Transport coherence from the source of a module-sheaf isomorphism to its target. -/
theorem of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N) [IsCoherent M] :
    IsCoherent N := sorry

/-- Coherence is equivalent on isomorphic module sheaves. -/
theorem iff_of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N) :
    IsCoherent M ↔ IsCoherent N := sorry

/-- A coherent sheaf of modules is finitely presented. Registering this canonical implication
lets downstream APIs consume coherence without rebuilding a local finite presentation. -/
@[stacks 01BW "coherent modules are finitely presented"]
instance isFinitePresentation
    (M : SheafOfModules.{w} R) [IsCoherent M] : M.IsFinitePresentation := sorry

end IsCoherent


end SheafOfModules
