module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Number
public import stacks_project.Chap72.Definition_72_18_3_Twist

/-!
# Compatibility checks for algebraic-space intersection numbers

The reusable intersection-number API is owned by the canonical ReasLib module.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Intersection

attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {k : Type u} [Field k]
variable {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
variable (i : Z ⟶ X) [IsClosedImmersion i] [Proper (SchemeRealization.toBase X)]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
variable (hZdim : dimension Z = d)
variable [Abelian X.Modules] [Abelian Z.Modules]
variable [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
variable [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
variable (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
variable (L0 : X.Modules) [isInvertibleObject L0]

#check (number i hZdim L : ℚ)
#check (existsUniqueNumericalPolynomial i hZdim L :
  ∃! P : MvPolynomial (Fin d) ℚ,
    MvPolynomial.totalDegree P ≤ d ∧ ∀ n : Fin d → ℤ,
      MvPolynomial.eval (fun j : Fin d ↦ (n j : ℚ)) P = (eulerCharacteristic i L n : ℚ))
#check (selfNumber i hZdim L0 : ℚ)

end AlgebraicGeometry.AlgebraicSpace.Modules.Intersection
