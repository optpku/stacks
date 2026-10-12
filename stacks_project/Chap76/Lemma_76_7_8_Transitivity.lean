/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap76.Lemma_76_7_6_Comparison

/-!
# Transitivity for relative differentials of algebraic spaces

For composable morphisms `X ⟶ Y ⟶ B` of algebraic spaces over a scheme `S`, the
canonical comparison morphisms of Lemma 76.7.6 form the right-exact transitivity sequence

  `(Modules.pullback f).obj (relativeDifferentials g) ⟶ relativeDifferentials (f ≫ g) ⟶
  relativeDifferentials f ⟶ 0`.

The maps and short complex are explicit data; exactness and epimorphy are recorded
separately.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.Transitivity

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S}

/-- The canonical map `(Modules.pullback f).obj (relativeDifferentials g) ⟶
relativeDifferentials (f ≫ g)` for composable morphisms of algebraic spaces. -/
noncomputable def baseChange (f : X ⟶ Y) (g : Y ⟶ B) :
    (Modules.pullback f).obj (relativeDifferentials g) ⟶ relativeDifferentials (f ≫ g) :=
  comparison f (𝟙 B) g (f ≫ g) (Eq.symm (Category.comp_id (f ≫ g)))

/-- `baseChange` is the differential comparison of the identity square on `B`. -/
theorem baseChange_eq (f : X ⟶ Y) (g : Y ⟶ B) :
    baseChange f g =
      comparison f (𝟙 B) g (f ≫ g) (Eq.symm (Category.comp_id (f ≫ g))) :=
  sorry

/-- The left transitivity morphism is the differential comparison attached to the identity
square on `B`. -/
theorem baseChange_isComparison (f : X ⟶ Y) (g : Y ⟶ B) :
    IsComparison f g (f ≫ g) (baseChange f g) :=
  sorry

/-- The canonical map `relativeDifferentials (f ≫ g) ⟶ relativeDifferentials f` for
composable morphisms of algebraic spaces. -/
noncomputable def projection (f : X ⟶ Y) (g : Y ⟶ B) :
    relativeDifferentials (f ≫ g) ⟶ relativeDifferentials f :=
  (SmallEtaleModuleGlueing.modulesPullbackId X).inv.app (relativeDifferentials (f ≫ g)) ≫
    comparison (𝟙 X) g (f ≫ g) f (Category.id_comp (f ≫ g))

/-- `projection` is identity-pullback transport of the differential comparison of the identity
square on `X`. -/
theorem projection_eq (f : X ⟶ Y) (g : Y ⟶ B) :
    projection f g =
      (SmallEtaleModuleGlueing.modulesPullbackId X).inv.app (relativeDifferentials (f ≫ g)) ≫
        comparison (𝟙 X) g (f ≫ g) f (Category.id_comp (f ≫ g)) :=
  sorry

/-- A morphism is the right transitivity morphism when it sends every universal
`B`-relative differential to the corresponding `Y`-relative differential. -/
def IsProjection (f : X ⟶ Y) (g : Y ⟶ B)
    (tau : relativeDifferentials (f ≫ g) ⟶ relativeDifferentials f) : Prop :=
  ∀ {U : (smallEtaleSite X)ᵒᵖ} (t : (commStructureSheaf X).obj.obj U),
    tau.val.app U ((universalDerivation (f ≫ g)).d t) = (universalDerivation f).d t

/-- The canonical transitivity projection satisfies its generator characterization. -/
theorem projection_isProjection (f : X ⟶ Y) (g : Y ⟶ B) :
    IsProjection f g (projection f g) :=
  sorry

/-- The canonical transitivity maps of relative differentials have zero composite. -/
theorem baseChange_comp_projection (f : X ⟶ Y) (g : Y ⟶ B) :
    baseChange f g ≫ projection f g = 0 :=
  sorry

/-- The canonical transitivity short complex for relative differentials of composable
morphisms of algebraic spaces. -/
noncomputable def complex (f : X ⟶ Y) (g : Y ⟶ B) : ShortComplex X.Modules :=
  ShortComplex.mk (baseChange f g) (projection f g) (baseChange_comp_projection f g)

/-- `complex` is the short complex on `baseChange` and `projection`. -/
theorem complex_eq (f : X ⟶ Y) (g : Y ⟶ B) :
    complex f g =
      ShortComplex.mk (baseChange f g) (projection f g) (baseChange_comp_projection f g) :=
  sorry

/-- The canonical transitivity short complex of two morphisms of algebraic spaces is
exact. -/
theorem exact (f : X ⟶ Y) (g : Y ⟶ B) : (complex f g).Exact :=
  sorry

/-- The projection in the transitivity sequence of relative differentials of algebraic
spaces is an epimorphism. -/
instance projection_epi (f : X ⟶ Y) (g : Y ⟶ B) : Epi (projection f g) :=
  sorry

/-- For two composable morphisms of algebraic spaces, the canonical transitivity complex of
relative differentials is exact and its projection is an epimorphism. -/
theorem exact_and_epi (f : X ⟶ Y) (g : Y ⟶ B) :
    (complex f g).Exact ∧ Epi (projection f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.Transitivity
