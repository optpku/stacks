module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Vanishing
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of pushforwards of injective module sheaves

Pushforwards of injective module sheaves are Cech-acyclic, hence their underlying additive sheaves
have vanishing positive cohomology on every open subset.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCohomology

variable {X Y : RingedSpace.{u}}

/-- Lemma 20.11.10 (2) (01EX): positive cohomology of the pushforward of an injective module
sheaf vanishes on every open subset of the target. -/
@[stacks 01EX "higher cohomology of an injective pushforward"]
theorem isZero_pushforward_of_injective
    (f : X ⟶ Y) {I : X.Modules} [Injective I]
    (V : Opens Y.carrier) {p : ℕ} (hp : 0 < p) :
    IsZero (((moduleUnderlyingSheaf Y).obj ((Hom.pushforward f).obj I)).H' p V) := sorry

/-- Module-valued form of the 01EX vanishing statement, retaining the section-ring action on the
cohomology over `V`. -/
@[stacks 01EX "module-valued higher cohomology of an injective pushforward"]
theorem isZero_module_pushforward_of_injective
    (f : X ⟶ Y) {I : X.Modules} [Injective I]
    (V : Opens Y.carrier) {p : ℕ} (hp : 0 < p) :
    IsZero (moduleCohomologyAtOpen V ((Hom.pushforward f).obj I) p) := sorry

end AlgebraicGeometry.RingedSpace.ModuleCohomology

