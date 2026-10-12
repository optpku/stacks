/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.Injectivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules.relativeAssassin

/- Lemma 38.23.1 (1): if a flat morphism `g : X' ⟶ X` over `S` covers the relative
associated points of a finite-type quasicoherent module `F` that is flat over `S`, then the
unit `F ⟶ g_* g^* F` is a monomorphism. -/
@[stacks 05PD]
#check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.unit_mono_of_subset_range :
    ∀ {S : Scheme.{u}} (X X' : Over S) (g : X' ⟶ X)
      [Flat g.left] [LocallyOfFiniteType X.hom] (F : X.left.Modules)
      [F.IsQuasicoherent] [F.IsFiniteType]
      [SheafOfModules.IsFlatOver F X.hom.toShHom]
      (_ : relativeAssassin X.hom F ⊆ Set.range g.left),
      Mono ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app F))

/- Lemma 38.23.1 (2): under the same hypotheses, after every base change `s : T ⟶ S`,
the unit for the base-changed module and morphism remains a monomorphism. -/
@[stacks 05PD]
#check
  (AlgebraicGeometry.Scheme.Modules.relativeAssassin.unit_mono_afterBaseChange_of_subset_range :
    ∀ {S : Scheme.{u}} (X X' : Over S) (g : X' ⟶ X)
      [Flat g.left] [LocallyOfFiniteType X.hom] (F : X.left.Modules)
      [F.IsQuasicoherent] [F.IsFiniteType]
      [SheafOfModules.IsFlatOver F X.hom.toShHom]
      (_ : relativeAssassin X.hom F ⊆ Set.range g.left)
      {T : Scheme.{u}} (s : T ⟶ S),
      Mono ((Scheme.Modules.pullbackPushforwardAdjunction ((Over.pullback s).map g).left).unit.app
        (Scheme.Modules.baseChangeModule X.hom s F)))

end Scheme.Modules.relativeAssassin
end AlgebraicGeometry
