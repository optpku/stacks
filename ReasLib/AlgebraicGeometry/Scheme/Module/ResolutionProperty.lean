/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

/-!
# The resolution property for schemes

The resolution property expresses the existence of finite locally free epimorphic
presentations of finite-type quasi-coherent modules on a scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme has the resolution property if every finite-type quasi-coherent module is a
quotient of a finite locally free module. -/
def HasResolutionProperty (X : Scheme.{u}) : Prop :=
  ∀ (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
    ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree) (q : E ⟶ F), Epi q

/-- The resolution property is characterized by finite locally free epimorphic presentations
of finite-type quasi-coherent modules. -/
theorem hasResolutionProperty_iff (X : Scheme.{u}) :
    HasResolutionProperty X ↔
      ∀ (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType],
        ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree) (q : E ⟶ F), Epi q := sorry

/-- A scheme with the resolution property supplies a finite locally free epimorphic
presentation of any finite-type quasi-coherent module. -/
theorem HasResolutionProperty.existsQuotient {X : Scheme.{u}}
    (hX : HasResolutionProperty X) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree) (q : E ⟶ F), Epi q := sorry

end AlgebraicGeometry.Scheme
