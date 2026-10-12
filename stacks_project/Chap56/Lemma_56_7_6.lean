/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport.PushforwardInvertible
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 56.7.6: for a finite-type separated morphism `f : X ⟶ Y` and a finite-type
quasicoherent module `F` whose scheme-theoretic support is finite over `Y`, if the
pushforward `(Scheme.Modules.pushforward f).obj F` is invertible, then `f` has a
section `s` and `F` is isomorphic to its pushforward along `s`. -/
@[stacks 0FZP] #check (AlgebraicGeometry.Scheme.Modules.exists_section_pushforward_iso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [f.FiniteType] [IsSeparated f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (h_support : IsFinite ((Scheme.Modules.schemeTheoreticSupport F).subschemeι ≫ f))
    [Scheme.Modules.Invertible ((Scheme.Modules.pushforward f).obj F)],
    ∃ s : Y ⟶ X, s ≫ f = 𝟙 Y ∧
      Nonempty (F ≅ (Scheme.Modules.pushforward s).obj
        ((Scheme.Modules.pushforward f).obj F)))

end AlgebraicGeometry.Scheme.Modules
