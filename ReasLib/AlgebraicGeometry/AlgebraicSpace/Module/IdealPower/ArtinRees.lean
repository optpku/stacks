module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower

/-!
# Artin–Rees for modules on algebraic spaces

Coherent modules on Noetherian algebraic spaces satisfy the Artin–Rees equality
for quasi-coherent subobjects and quasi-coherent ideal sheaves.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a coherent module `F` on a Noetherian algebraic space, a quasi-coherent
subobject `G`, and a quasi-coherent ideal sheaf `I`, there exists a natural number
`c` such that `I^(n-c)(I^c F ∩ G) = I^n F ∩ G` as subobjects of `F` for every
`n ≥ c`. -/
@[stacks 07UL]
theorem exists_artinReesConstant
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent] (G : Subobject F)
    [((G : X.Modules)).IsQuasicoherent] (I : IdealSubobject X) [IsQuasiCoherent I] :
    ∃ c : ℕ, ∀ n ≥ c,
      idealPowerSmulSubobject I ((idealPowerProductSubobject I F c) ⊓ G) (n - c) =
        idealPowerProductSubobject I F n ⊓ G :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
