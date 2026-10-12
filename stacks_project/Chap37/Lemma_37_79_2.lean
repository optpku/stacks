/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.QuasiAffine
public import stacks_project.Chap37.Lemma_37_79_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.Modules
namespace AmpleFamily

/- Lemma 37.79.2: a quasi-affine morphism of schemes transfers the existence of an
ample family of invertible modules from its target to its source. -/
@[stacks 0GTQ]
#check (AlgebraicGeometry.Scheme.Modules.AmpleFamily.exists_of_quasiAffineHom :
  ∀ {X Y : Scheme.{u}} {ι : Type v} (f : X ⟶ Y) (M : ι → Y.Modules)
    (hM : AmpleFamily M) (hf : QuasiAffineHom f),
    ∃ (κ : Type (max u v)) (N : κ → X.Modules), AmpleFamily N)

/- The affine specialization of the ample-family transfer theorem. -/
#check (AlgebraicGeometry.Scheme.Modules.AmpleFamily.exists_of_isAffineHom :
  ∀ {X Y : Scheme.{u}} {ι : Type v} (f : X ⟶ Y) [IsAffineHom f]
    (M : ι → Y.Modules) (hM : AmpleFamily M),
    ∃ (κ : Type (max u v)) (N : κ → X.Modules), AmpleFamily N)

end AmpleFamily
end AlgebraicGeometry.Scheme.Modules
