module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FunctionField
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.List.TFAE

/-!
# Torsion of local sections

This file relates pointwise torsion of the germs of a section on an integral scheme to
vanishing in the generic stalk and in the associated generic-point skyscraper sheaf.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.SectionTorsion

variable {X : Scheme.{u}} [hX : IsIntegral X]

/-- The canonical generic point, regarded as a point of a nonempty open subset. -/
def genericPointInOpen {U : X.Opens} (hU : Set.Nonempty (U : Set X)) : U :=
  ⟨genericPoint X,
    ((genericPoint_spec X).mem_open_set_iff U.2).2 (by
      simpa [Set.inter_univ] using hU)⟩

/-- A section is torsion at a point when its germ belongs to the torsion submodule of the
corresponding stalk. -/
def IsAt (ℱ : X.Modules) {U : X.Opens} (s : ℱ.val.obj (op U)) (x : U) : Prop :=
  TopCat.Presheaf.germ ℱ.val.presheaf U x.1 x.2 s ∈
    Submodule.torsion (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)

include hX in
/-- A local section is torsion when its germ is torsion at every point of its domain. -/
def Is (ℱ : X.Modules) {U : X.Opens} (s : ℱ.val.obj (op U)) : Prop :=
  ∀ x : U, IsAt ℱ s x

/-- The germ of a section at the canonical generic point of an integral scheme. -/
def genericGerm (ℱ : X.Modules) {U : X.Opens} (hU : Set.Nonempty (U : Set X))
    (s : ℱ.val.obj (op U)) :
    RingedSpace.stalkModuleCat ℱ (genericPoint X) :=
  TopCat.Presheaf.germ ℱ.val.presheaf U (genericPoint X) (genericPointInOpen hU).2 s

/-- The pushforward to an integral scheme of a module pulled back to its generic point. -/
def genericSkyscraper (ℱ : X.Modules) : X.Modules :=
  (RingedSpace.Module.Skyscraper.functor (genericPoint X)).obj
    ((RingedSpace.Module.pointPullbackFunctor (genericPoint X)).obj ℱ)

/-- The image of a section under the adjunction unit into the generic-point skyscraper module. -/
def genericSkyscraperImage (ℱ : X.Modules) {U : X.Opens} (s : ℱ.val.obj (op U)) :
    (genericSkyscraper ℱ).val.obj (op U) :=
  (((RingedSpace.Module.Skyscraper.adjunction (genericPoint X)).unit.app ℱ).val.app
    (op U)).hom s

/-- A section over a nonempty open has a torsion germ at some point exactly when its generic germ
vanishes. -/
theorem exists_isAt_iff_genericGerm_eq_zero (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    (∃ x : U, IsAt ℱ s x) ↔ genericGerm ℱ hU s = 0 := sorry

/-- A section over a nonempty open has torsion germ at every point exactly when its generic germ
vanishes. -/
theorem forall_isAt_iff_genericGerm_eq_zero (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    (∀ x : U, IsAt ℱ s x) ↔ genericGerm ℱ hU s = 0 := sorry

/-- Vanishing of a section's generic germ is equivalent to vanishing of its image in the
generic-point skyscraper sheaf. -/
theorem genericGerm_eq_zero_iff_genericSkyscraperImage_eq_zero
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    genericGerm ℱ hU s = 0 ↔ genericSkyscraperImage ℱ s = 0 := sorry

/-- Pointwise torsion of a section at some point or at every point, vanishing of its generic
germ, and vanishing of its generic-point skyscraper image are equivalent. -/
theorem tfae (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    List.TFAE [
      ∃ x : U, IsAt ℱ s x,
      ∀ x : U, IsAt ℱ s x,
      genericGerm ℱ hU s = 0,
      genericSkyscraperImage ℱ s = 0] := sorry

end AlgebraicGeometry.Scheme.Modules.SectionTorsion

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [hX : IsIntegral X]

include hX in
/-- A module sheaf on an integral scheme is torsion free when every torsion local section
vanishes. -/
class IsTorsionFree (ℱ : X.Modules) : Prop where
  /-- Every torsion local section vanishes. -/
  eq_zero_of_isTorsionSection :
    ∀ ⦃U : X.Opens⦄ (s : ℱ.val.obj (op U)), SectionTorsion.Is ℱ s → s = 0

omit hX in
/-- A quasicoherent module sheaf is torsion free exactly when every torsion local section
vanishes. -/
theorem isTorsionFree_iff_forall_isTorsion_eq_zero
    [IsIntegral X] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsTorsionFree ℱ ↔
      ∀ ⦃U : X.Opens⦄ (s : ℱ.val.obj (op U)), SectionTorsion.Is ℱ s → s = 0 := by
  constructor
  · intro hℱ
    simpa using hℱ.eq_zero_of_isTorsionSection
  · intro hℱ
    exact ⟨hℱ⟩

/-- A zero module sheaf on an integral scheme is torsion free. -/
instance instIsTorsionFreeOfIsZero : IsTorsionFree (0 : X.Modules) where
  eq_zero_of_isTorsionSection := sorry

end AlgebraicGeometry.Scheme.Modules
