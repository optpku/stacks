module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Topology.KrullDimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.GrothendieckLarge

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A dualizing sheaf on a proper scheme of dimension `d` over a field `k` is a
finitely presented module `ω` with a trace on degree-`d` cohomology such that
composition with the trace identifies morphisms into `ω` with `k`-linear maps
from degree-`d` cohomology to `k`, for every finitely presented module. -/
def IsDualizingSheaf {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (d : ℕ) (ω : X.Modules) : Prop :=
  let H : X.Modules ⥤ ModuleCat k :=
    (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (Opposite.op ⊤)).rightDerived d ⋙
      ModuleCat.restrictScalars (((Scheme.ΓSpecIso (CommRingCat.of k)).inv) ≫ f.appTop).hom
  IsProper f ∧ topologicalKrullDim X = d ∧ ω.IsFinitePresentation ∧
    ∃ trace : H.obj ω ⟶ ModuleCat.of k k,
      ∀ F : X.Modules, F.IsFinitePresentation →
        Function.Bijective (fun φ : F ⟶ ω => H.map φ ≫ trace)

end AlgebraicGeometry.Scheme
