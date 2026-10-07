module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap59.Remark_59_56_6_StalkFunctor
public import stacks_project.Chap59.Theorem_59_56_3

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {S : Scheme.{u}}

/-- Remark 59.56.6 (1): if `s̄ : Spec k → S` is a geometric point, then `k` is
algebraically closed, so the absolute Galois group of `k` is trivial. -/
@[stacks 04JN]
instance sourceField_galoisGroup_unique (s : GeometricPoint S) :
    Subsingleton (s.K ≃ₐ[s.K] s.K) :=
  sorry

/-- The residue-field absolute Galois group of a geometric point is likewise trivial. -/
instance absoluteGaloisGroup_unique (s : GeometricPoint S) :
    Subsingleton s.absoluteGaloisGroup :=
  sorry

end AlgebraicGeometry.Scheme.GeometricPoint

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}}

/-- Remark 59.56.6 (2): for an algebraically closed field `k`, sheaves on
`Spec k_étale` are equivalent to sets, via sections over `Spec k`. -/
@[stacks 04JN]
def etaleSheavesEquivType (K : Type u) [Field K] [IsAlgClosed K]
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology (Type u)] :
    Sheaf (Spec (.of K)).smallEtaleTopology (Type u) ≌ Type u where
  functor :=
    (GeometricPoint.toSmallEtalePoint
      (@GeometricPoint.of (Spec (.of K)) K inferInstance inferInstance (𝟙 _))).sheafFiber
  inverse := constantSheaf (Spec (.of K)).smallEtaleTopology (Type u)
  unitIso := NatIso.ofComponents (fun F ↦ eqToIso sorry) (fun {F G} f ↦ sorry)
  counitIso := NatIso.ofComponents (fun X ↦ eqToIso sorry) (fun {X Y} f ↦ sorry)

/-- The equivalence of Remark 59.56.6 (2) sends a sheaf to its fibre at the
identity geometric point of `Spec k`. -/
theorem etaleSheavesEquivType_functor_obj (K : Type u) [Field K] [IsAlgClosed K]
    [HasWeakSheafify (Spec (.of K)).smallEtaleTopology (Type u)]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type u)) :
    (etaleSheavesEquivType K).functor.obj F =
      (GeometricPoint.toSmallEtalePoint
        (@GeometricPoint.of (Spec (.of K)) K inferInstance inferInstance (𝟙 _))).sheafFiber.obj F :=
  sorry

variable (s : GeometricPoint S)
variable [HasWeakSheafify S.smallEtaleTopology (Type u)]
variable [HasWeakSheafify (Spec (.of s.K)).smallEtaleTopology (Type u)]
variable [∀ P : S.Etaleᵒᵖ ⥤ Type u, (smallEtalePullback s.hom).op.HasLeftKanExtension P]
variable [InitiallySmall
    ((smallEtalePullback s.hom ⋙
        (GeometricPoint.toSmallEtalePoint (idGeometricPoint s)).fiber).Elements)]
variable [((smallEtalePullback s.hom).sheafPushforwardContinuous (Type u)
    S.smallEtaleTopology (Spec (.of s.K)).smallEtaleTopology).IsRightAdjoint]

/-- Transport of sheaf fibres along the identification of `s̄` with
`id_{Spec k} ≫ s̄`. -/
def stalkFunctor_imagePointIso (F : Sheaf S.smallEtaleTopology (Type u)) :
    (GeometricPoint.toSmallEtalePoint
        (smallEtaleInverseImage_imagePoint s.hom (idGeometricPoint s))).sheafFiber.obj F ≅
      (stalkFunctor s).obj F :=
  eqToIso sorry

/-- Remark 59.56.6 (3): the stalk functor `F ↦ F_s̄` is isomorphic to
`F ↦ s̄^* F`, identified with a set via sections over `Spec k`. This is
Lemma 59.36.2 (3) for `f = s̄`. -/
@[stacks 04JN]
def stalkFunctorIsoPullback :
    stalkFunctor s ≅ pullbackThenSections s :=
  NatIso.ofComponents
    (fun F ↦
      (stalkFunctor_imagePointIso s F).symm.trans
        (smallEtaleInverseImage_stalkIso s.hom (idGeometricPoint s) F).symm)
    (fun {F G} f ↦ sorry)

/-- Componentwise, the alternative stalk identification is
`F_s̄ ≅ (s̄^* F)` evaluated at the identity geometric point of `Spec k`. -/
theorem stalkFunctorIsoPullback_app (F : Sheaf S.smallEtaleTopology (Type u)) :
    (stalkFunctorIsoPullback s).app F =
      (stalkFunctor_imagePointIso s F).symm.trans
        (smallEtaleInverseImage_stalkIso s.hom (idGeometricPoint s) F).symm :=
  sorry

end AlgebraicGeometry.Scheme.Etale
