/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.InternalHom.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections

/-! # Compatibility surface for the small étale internal Hom -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Bundle a function between module objects using its additivity and scalar-linearity proofs. -/
def moduleCatOfFun {R : Type u} [Ring R] (src tgt : ModuleCat.{u} R)
    (f : src → tgt)
    (hadd : ∀ x y, f (x + y) = f x + f y := by intros; rfl)
    (hsmul : ∀ (r : R) x, f (r • x) = r • f x := by intros; rfl) : src ⟶ tgt :=
  ModuleCat.ofHom { toFun := f, map_add' := hadd, map_smul' := hsmul }

/-- The small étale sheaf of local module morphisms, under its compatibility name. -/
abbrev moduleSheafHomOnEtale {S : Scheme.{u}} {X : GroupoidsOver S}
    (F G : etaleModules X) [F.IsFinitePresentation] : etaleModules X :=
  moduleSheafHomEtale F G

#check (AlgebraicGeometry.GroupoidsOver.moduleSheafHomOnEtale_homEquiv :
  {S : Scheme.{u}} → {X : GroupoidsOver S} →
    (F G H : etaleModules X) → [F.IsFinitePresentation] →
    (H ⟶ moduleSheafHomEtale F G) ≃ (moduleTensorEtale H F ⟶ G))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.internalHomFP :
  {S : Scheme.{u}} → {X : GroupoidsOver S} → [AlgebraicStack X] →
    (F : fppfModules X) → QCoh X → [F.IsFinitePresentation] → QCoh X)

end AlgebraicGeometry.GroupoidsOver
