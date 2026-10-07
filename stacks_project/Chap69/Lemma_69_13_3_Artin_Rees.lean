module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower

/-!
# Lemma 69.13.3 (Artin-Rees)

On a Noetherian algebraic space, a coherent module, a quasi-coherent subsheaf,
and a quasi-coherent ideal sheaf satisfy the Artin–Rees lemma.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 69.13.3 (Artin-Rees): let `S` be a scheme, let `X` be a Noetherian algebraic
space over `S`, let `F` be a coherent sheaf on `X`, let `G ⊂ F` be a quasi-coherent
subsheaf, and let `I ⊂ 𝒪_X` be a quasi-coherent sheaf of ideals. Then there exists
`c ≥ 0` such that for all `n ≥ c` one has
`I^(n-c)(I^c F ∩ G) = I^n F ∩ G` as subobjects of `F`. -/
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
