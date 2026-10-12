/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap50.Proposition_50_20_4_CohomologyTrace
public import stacks_project.Chap50.Lemma_50_20_3

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalClosed TopologicalSpace
open RingedSpace.ModuleDerived.KFlat RingedSite.Hom.DerivedAdjunction
open SheafOfModules.RingedSite.IntGraded
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

-- Local instance justification (defeq pin): imported cup products use the standard derived-category presentation.
attribute [local instance] HasDerivedCategory.standard
-- Local instance justification (search instability): cup products require the canonical integer-graded tensor theorem.
attribute [local instance] hasTensor

namespace AlgebraicGeometry.Scheme.DeRham

variable {k : Type u} [Field k] (X : SchemeOverField k) (d : ℕ)
-- Local instance justification (defeq pin): cup products use this canonical coefficient-sheaf monoidal structure.
noncomputable local instance : MonoidalCategory
    (RingedSpace.DeRham.Modules X.hom.toShHom) :=
  SheafOfModules.RingedSite.moduleMonoidalCategory
    (RingedSpace.DeRham.coefficients X.hom.toShHom)

-- Local instance justification (defeq pin): cup products use this standard totalized cochain monoidal structure.
noncomputable local instance : MonoidalCategory
    (CochainComplex (RingedSpace.DeRham.Modules X.hom.toShHom) ℤ) :=
  HomologicalComplex.monoidalCategory _ (ComplexShape.up ℤ)

variable [Nonempty X.left] [Smooth X.hom] [IsProper X.hom]
variable [EquidimensionalSpace X.left]
variable [HomotopyTensorDescends X.left.toRingedSpace]
variable [TensorDescends X.left.toRingedSpace]
variable [IsLocalization X.left.toRingedSpace]
variable [HomotopyTensorDescends (Spec (CommRingCat.of k)).toRingedSpace]
variable [TensorDescends (Spec (CommRingCat.of k)).toRingedSpace]
variable [IsLocalization (Spec (CommRingCat.of k)).toRingedSpace]
variable [HomotopyCategory.KFlat.HasResolutions X.left.Modules]
variable [HasPair (RingedSpace.opensRingedSiteHom X.hom.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived X.hom.toShHom)]
variable [MonoidalClosed
  (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
variable [derivedMonoidal : MonoidalCategory (coefficientDerived X.hom)]
variable [∀ G₁ G₂ : GradedObject ℤ (coefficientModules X.hom),
  GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules X.hom),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (coefficientModules X.hom),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (coefficientModules X.hom),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [qhMonoidal : Functor.Monoidal
  (DerivedCategory.Qh : HomotopyCategory (coefficientModules X.hom) (ComplexShape.up ℤ) ⥤
    coefficientDerived X.hom)]
variable [globalLaxMonoidal : (globalDerivedFunctor X.hom).LaxMonoidal]

/-- Proposition 50.20.4 (1): a nonempty smooth proper equidimensional `k`-scheme of
dimension `d` admits a `k`-linear trace on `H^(2 * d)_dR(X / k)` whose cup-trace pairing
is perfect in every integer degree. -/
@[stacks 0FW7]
theorem existsDeRhamPoincareTrace
    (h_dimension : topologicalKrullDim X.left = d)
    (T : CoefficientTensorModel X.hom) :
    ∃ t : cohomologyOverAffineBase X.hom (2 * (d : ℤ)) ⟶ ModuleCat.of k k,
      CohomologyTrace.IsPerfect X.hom T d t := sorry

/-- Proposition 50.20.4 (2): any two perfect top-degree de Rham traces differ by
precomposition with multiplication by a unit of `Γ(X.left, ⊤)`. -/
@[stacks 0FW7]
theorem deRhamPoincareTrace_unique
    (h_dimension : topologicalKrullDim X.left = d)
    (T : CoefficientTensorModel X.hom)
    (t t' : cohomologyOverAffineBase X.hom (2 * (d : ℤ)) ⟶ ModuleCat.of k k)
    (ht : CohomologyTrace.IsPerfect X.hom T d t)
    (ht' : CohomologyTrace.IsPerfect X.hom T d t') :
    ∃ u : Γ(X.left, ⊤)ˣ,
      t' = CohomologyTrace.unitAction X.hom (2 * (d : ℤ)) u ≫ t := sorry

end AlgebraicGeometry.Scheme.DeRham
