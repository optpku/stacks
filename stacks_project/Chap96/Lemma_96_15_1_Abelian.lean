module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Preadditive.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Definition_96_11_1_QCoh

/-!
# Abelian structure on quasi-coherent modules of an algebraic stack

For an algebraic stack `𝒳`, the category `QCoh(𝒪_𝒳)` is abelian, the inclusion
into `Mod(𝒪_𝒳)` preserves finite colimits, and quasi-coherent modules are
closed under extensions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The category `QCoh(𝒪_𝒳)` of an algebraic stack is abelian. -/
instance abelian [AlgebraicStack X] : Abelian (QCoh X) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The inclusion `QCoh(𝒪_𝒳) ⟶ Mod(𝒪_𝒳)` preserves finite colimits. -/
instance inclusion_preservesFiniteColimits [AlgebraicStack X] :
    PreservesFiniteColimits (inclusion X) :=
  sorry

/-- Quasi-coherent modules on an algebraic stack are closed under extensions in
`Mod(𝒪_𝒳)`. -/
instance closedUnderExtensions [AlgebraicStack X] :
    (quasiCoherentModuleProperty X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact := sorry

/-- In a short exact sequence in `Mod(𝒪_𝒳)`, if the outer terms are
quasi-coherent then so is the middle term. -/
theorem isQuasicoherent_of_shortExact [AlgebraicStack X]
    {sc : ShortComplex (RingedSite.ModuleCat.{u} (fppfRingedSite X))}
    (hsc : sc.ShortExact)
    (h₁ : quasiCoherentModuleProperty X sc.X₁)
    (h₃ : quasiCoherentModuleProperty X sc.X₃) :
    quasiCoherentModuleProperty X sc.X₂ :=
  sorry

/-- Colimits in `QCoh(𝒪_𝒳)` agree with colimits computed in `Mod(𝒪_𝒳)`. -/
def inclusion_colimitIso [AlgebraicStack X] {J : Type u} [Category.{u} J]
    (F : J ⥤ QCoh X)
    [HasColimit F] [HasColimit (F ⋙ inclusion X)]
    [PreservesColimit F (inclusion X)] :
    colimit (F ⋙ inclusion X) ≅ (inclusion X).obj (colimit F) :=
  (preservesColimitIso (inclusion X) F).symm

/-- `inclusion_colimitIso` is the inverse of `preservesColimitIso`. -/
theorem inclusion_colimitIso_eq [AlgebraicStack X] {J : Type u} [Category.{u} J]
    (F : J ⥤ QCoh X)
    [HasColimit F] [HasColimit (F ⋙ inclusion X)]
    [PreservesColimit F (inclusion X)] :
    inclusion_colimitIso F = (preservesColimitIso (inclusion X) F).symm :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
