module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.IdealPower
import StacksCheckRecall

/-!
# Lemma 69.13.2

A coherent module on a Noetherian algebraic space is annihilated by some power
of a quasi-coherent ideal sheaf if and only if its support is contained
set-theoretically in the corresponding closed subspace.
-/

universe u

/- Lemma 69.13.2: let `S` be a scheme, let `X` be a Noetherian algebraic space over
`S`, let `F` be a coherent sheaf on `X`, and let `I ⊂ 𝒪_X` be a quasi-coherent
sheaf of ideals corresponding to the closed subspace `Z = subscheme I`. Then
there is some `n ≥ 0` such that `I^n F = 0` if and only if `Supp(F) ⊆ |Z|`
set-theoretically, where `|Z|` is the image of `Points.map (subschemeι I)`. -/
@[stacks 07UK]
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.exists_idealPowerProductSubobject_eq_bot_iff_moduleSupport_subset :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
      [AlgebraicGeometry.AlgebraicSpace.IsNoetherian X]
      (F : X.Modules) [F.IsCoherent] (I : AlgebraicGeometry.AlgebraicSpace.IdealSubobject X)
      [AlgebraicGeometry.AlgebraicSpace.IsQuasiCoherent I],
      (∃ n : ℕ, AlgebraicGeometry.AlgebraicSpace.Modules.idealPowerProductSubobject I F n = ⊥) ↔
        AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupport F ⊆
          Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map
            (AlgebraicGeometry.AlgebraicSpace.subschemeι I)))
