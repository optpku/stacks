module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.FiberFamily
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Example 62.5.2: Let `f : X ⟶ S` be a morphism of schemes which is locally of finite type.
Let `r ≥ 0` be an integer. Let `F` be a quasi-coherent `O_X`-module of finite type. For
`s ∈ S` denote `F_s` the pullback of `F` to `X_s`. Assume `dim(Supp(F_s)) ≤ r` for all
`s ∈ S`. Then we associate to `F` the family `[F/X/S]_r` of `r`-cycles on fibres of
`X/S` defined by `[F/X/S]_r = ([F_s]_r)_{s ∈ S}`, where `[F_s]_r` is given by Chow
Homology, Definition 42.10.2. -/
@[stacks 0H4Q]
#check (AlgebraicGeometry.Scheme.Hom.moduleFiberCycleFamily :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] →
    (F : X.Modules) → [F.IsQuasicoherent] → [F.IsFiniteType] →
    (r : ℕ) → f.fiberModuleSupportDimensionLE F r → f.FiberCycleFamily (r : ℤ))
