/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import stacks_project.Chap103.Lemma_103_16_3_QCoh

/-!
# Lemma 103.16.4

On an algebraic stack, quasi-coherent modules on the lisse-étale site form a
weak Serre subcategory of all lisse-étale modules, and likewise on the
flat-fppf site.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The category of lisse-étale `𝒪`-modules on an algebraic stack is abelian. -/
instance lisseEtaleModules_abelian (X : GroupoidsOver S) [AlgebraicStack X] :
    Abelian (SheafOfModules.{u} (lisseEtaleStructureSheaf X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The category of flat-fppf `𝒪`-modules on an algebraic stack is abelian. -/
instance flatFppfModules_abelian (X : GroupoidsOver S) [AlgebraicStack X] :
    Abelian (SheafOfModules.{u} (flatFppfStructureSheaf X)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

namespace lisseEtaleQCoh

/-- Lemma 103.16.4 (1): let `X` be an algebraic stack. Then
`lisseEtaleQCoh X` is a weak Serre subcategory of
`SheafOfModules (lisseEtaleStructureSheaf X)`. -/
@[stacks 07B4]
instance isWeakSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleQuasiCoherent X).IsWeakSerreClass :=
  sorry

/-- The inclusion `lisseEtaleQCoh X ⥤ SheafOfModules (lisseEtaleStructureSheaf X)`
is exact. -/
theorem inclusion_exact (X : GroupoidsOver S) [AlgebraicStack X] :
    exactFunctor (lisseEtaleQCoh X) (SheafOfModules.{u} (lisseEtaleStructureSheaf X))
      (lisseEtaleQCoh.inclusion X) :=
  sorry

/-- The kernel of a morphism of quasi-coherent lisse-étale modules is
quasi-coherent. -/
instance isQuasicoherent_kernel {X : GroupoidsOver S} [AlgebraicStack X]
    {F G : SheafOfModules.{u} (lisseEtaleStructureSheaf X)}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (kernel f).IsQuasicoherent :=
  sorry

/-- The cokernel of a morphism of quasi-coherent lisse-étale modules is
quasi-coherent. -/
instance isQuasicoherent_cokernel {X : GroupoidsOver S} [AlgebraicStack X]
    {F G : SheafOfModules.{u} (lisseEtaleStructureSheaf X)}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (cokernel f).IsQuasicoherent :=
  sorry

end lisseEtaleQCoh

namespace flatFppfQCoh

/-- Lemma 103.16.4 (2): let `X` be an algebraic stack. Then
`flatFppfQCoh X` is a weak Serre subcategory of
`SheafOfModules (flatFppfStructureSheaf X)`. -/
@[stacks 07B4]
instance isWeakSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfQuasiCoherent X).IsWeakSerreClass :=
  sorry

/-- The inclusion `flatFppfQCoh X ⥤ SheafOfModules (flatFppfStructureSheaf X)`
is exact. -/
theorem inclusion_exact (X : GroupoidsOver S) [AlgebraicStack X] :
    exactFunctor (flatFppfQCoh X) (SheafOfModules.{u} (flatFppfStructureSheaf X))
      (flatFppfQCoh.inclusion X) :=
  sorry

/-- The kernel of a morphism of quasi-coherent flat-fppf modules is
quasi-coherent. -/
instance isQuasicoherent_kernel {X : GroupoidsOver S} [AlgebraicStack X]
    {F G : SheafOfModules.{u} (flatFppfStructureSheaf X)}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (kernel f).IsQuasicoherent :=
  sorry

/-- The cokernel of a morphism of quasi-coherent flat-fppf modules is
quasi-coherent. -/
instance isQuasicoherent_cokernel {X : GroupoidsOver S} [AlgebraicStack X]
    {F G : SheafOfModules.{u} (flatFppfStructureSheaf X)}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (f : F ⟶ G) :
    (cokernel f).IsQuasicoherent :=
  sorry

end flatFppfQCoh

end AlgebraicGeometry.AlgebraicStack
