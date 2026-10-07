module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import stacks_project.Chap61.Example_61_19_12_Function
public import stacks_project.Chap61.Lemma_61_19_1_Comparison
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Example 61.19.12

The sheaf of all point-set maps on the small pro-étale site, the short exact
sequence measuring failure of local constancy, comparison of constant sheaves
along `ε⁻¹`, and vanishing of `H¹` on affines with closed separably closed
points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Example 61.19.12 (1): on `X.ProEt`, `fun(-, A)` is the abelian sheaf of all
point-set maps `U.left → A`. -/
@[stacks 0F6D] #check AlgebraicGeometry.Scheme.ProEt.functionSheaf

namespace AlgebraicGeometry.Scheme.ProEt

/-- Example 61.19.12 (2): the sequence `0 ⟶ underline(A) ⟶ fun(-, A) ⟶ F ⟶ 0`
of abelian sheaves on `X.ProEt` is short exact, where `F` is the sheaf
cokernel of `constantToFunction`. -/
@[stacks 0F6D]
theorem functionsModLocallyConstantSequence_shortExact
    (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    (functionsModLocallyConstantSequence X A).ShortExact :=
  sorry

/-- Example 61.19.12 (3): the constant sheaf `underline(A)` on `X.ProEt` is
isomorphic to `ε⁻¹ underline(A)`, the inverse image of the constant sheaf on
`X.Etale`. -/
@[stacks 0F6D]
theorem constantSheaf_etaleToProEtPullback_isIsomorphic
    (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    IsIsomorphic
      ((etaleToProEtPullback X AddCommGrpCat.{u + 1}).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of A)))
      ((constantSheaf (topology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A)) :=
  sorry

/-- Example 61.19.12 (4): if `X` is nonempty and `A` is nontrivial, then
`fun(-, A)` does not lie in the essential image of `ε⁻¹`. -/
@[stacks 0F6D]
theorem functionSheaf_not_mem_essImage
    (X : Scheme.{u}) (hX : Nonempty X) (A : Type (u + 1)) [AddCommGroup A] [Nontrivial A]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    ¬ (etaleToProEtPullback X AddCommGrpCat.{u + 1}).essImage (functionSheaf X A) :=
  sorry

/-- Example 61.19.12 (5): if `X` is nonempty and `A` is nontrivial, then the
cokernel sheaf `F` does not lie in the essential image of `ε⁻¹`. -/
@[stacks 0F6D]
theorem functionsModLocallyConstant_not_mem_essImage
    (X : Scheme.{u}) (hX : Nonempty X) (A : Type (u + 1)) [AddCommGroup A] [Nontrivial A]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    ¬ (etaleToProEtPullback X AddCommGrpCat.{u + 1}).essImage
        (functionsModLocallyConstant X A) :=
  sorry

/-- Closed points of `X` remain closed on a weakly étale `U` over `X`. -/
theorem isClosed_singleton_of_weaklyEtale (X : Scheme.{u}) (U : X.ProEt)
    (h_closed : ∀ x : X, IsClosed ({x} : Set X)) (x : U.left) :
    IsClosed ({x} : Set U.left) :=
  sorry

/-- Separably closed residue fields of `X` remain separably closed on a weakly
étale `U` over `X`. -/
theorem isSepClosed_residueField_of_weaklyEtale (X : Scheme.{u}) (U : X.ProEt)
    (h_res : ∀ x : X, IsSepClosed (X.residueField x)) (x : U.left) :
    IsSepClosed (U.left.residueField x) :=
  sorry

/-- Example 61.19.12 (6): if `Y` is affine, every point of `Y` is closed, and
every residue field of `Y` is separably closed, then
`H¹_étale(Y, underline(A)) = 0`, by Étale Cohomology, Lemma 59.80.3. -/
@[stacks 0F6D]
theorem etaleH1_constant_isZero (Y : Scheme.{u}) [IsAffine Y]
    (h_closed : ∀ y : Y, IsClosed ({y} : Set Y))
    (h_res : ∀ y : Y, IsSepClosed (Y.residueField y))
    (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    IsZero ((Sheaf.functorH Y.smallEtaleTopology 1).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A))) :=
  sorry

/-- Example 61.19.12 (7): under the same hypotheses on `Y`,
`H¹_proétale(Y, underline(A)) = 0`, by Lemma 61.19.6 and
Étale Cohomology, Lemma 59.80.3. -/
@[stacks 0F6D]
theorem proEtH1_constant_isZero (Y : Scheme.{u}) [IsAffine Y]
    (h_closed : ∀ y : Y, IsClosed ({y} : Set Y))
    (h_res : ∀ y : Y, IsSepClosed (Y.residueField y))
    (A : Type (u + 1)) [AddCommGroup A]
    [HasSheafify (topology Y) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (topology Y) AddCommGrpCat.{u + 1})] :
    IsZero ((Sheaf.functorH (topology Y) 1).obj
      ((constantSheaf (topology Y) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of A))) :=
  sorry

/-- Example 61.19.12 (8): if every point of `X` is closed with separably closed
residue field and `U` is affine on `X.ProEt`, then the sections of `F` at `U`
are isomorphic to the cokernel of `underline(A)(U) ⟶ fun(U, A)`. -/
@[stacks 0F6D]
theorem functionsModLocallyConstant_sections
    (X : Scheme.{u}) (A : Type (u + 1)) [AddCommGroup A]
    (h_closed : ∀ x : X, IsClosed ({x} : Set X))
    (h_res : ∀ x : X, IsSepClosed (X.residueField x))
    (U : X.ProEt) [IsAffine U.left]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}] :
    IsIsomorphic ((functionsModLocallyConstant X A).obj.obj (op U))
      (cokernel ((constantToFunction X A).hom.app (op U))) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
