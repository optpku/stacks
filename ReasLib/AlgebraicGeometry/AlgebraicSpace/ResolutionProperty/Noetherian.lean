/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Descent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Power
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty

/-!
# Resolution property of Noetherian algebraic spaces

On a Noetherian algebraic space with affine étale descent data, every coherent
module is a quotient of a finite coproduct of pushforwards of powers of the
descent ideal. The resolution
property is equivalent to a finite locally free presentation of the associated
pushforward ideal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ResolutionDescent

/-- Every coherent module on a Noetherian algebraic space with affine étale descent
data is a quotient of a finite coproduct of pushforwards of nonnegative powers of
the descent ideal. -/
@[stacks 0GUZ]
theorem exists_epi_coproduct_pushforward_pow
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (sit : ResolutionDescent X) (F : X.Modules) [F.IsCoherent] :
    ∃ (r : ℕ) (n : Fin r → ℕ)
      (q : (∐ fun i : Fin r ↦
        (Modules.pushforward sit.π).obj (sit.I.pow (n i)).toModule) ⟶ F),
      Epi q :=
  sorry

/-- A Noetherian algebraic space has the resolution property exactly when the
pushforward of the descent ideal admits a finite locally free epimorphic presentation. -/
@[stacks 0GV0]
theorem hasResolutionProperty_iff_pushforward_ideal
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (sit : ResolutionDescent X) :
    SheafOfModules.HasResolutionProperty (structureSheaf X) ↔
      ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
        (q : E ⟶ (Modules.pushforward sit.π).obj sit.I.toModule),
        Epi q :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ResolutionDescent
