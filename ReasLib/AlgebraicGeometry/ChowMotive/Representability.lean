module

public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.ChowMotive.ChowGroup
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Yoneda

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Correspondence

noncomputable section

universe u

namespace ChowMotive

variable {k : Type u} [Field k]

/-- The projector action on rational Chow groups is functorial in motives. -/
theorem chowFunctor_map_mem (i : ℤ)
    {M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)} (c : M ⟶ N) :
    ∀ x ∈ LinearMap.range ((chowRealization k i).map M.p).hom,
      ((chowRealization k i).map c.f).hom x ∈
        LinearMap.range ((chowRealization k i).map N.p).hom := by
  sorry

/-- The degree-`i` Chow-group functor on rational Chow motives. -/
noncomputable def chowFunctor (k : Type u) [Field k] (i : ℤ) :
    ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤ ModuleCat.{u + 1} ℚ where
  obj M := chowGroup M i
  map {M N} c := ModuleCat.ofHom
    (((chowRealization k i).map c.f).hom.restrict (chowFunctor_map_mem i c))
  map_id := by
    sorry
  map_comp := by
    sorry

/-- The object part of `chowFunctor` is the concrete projector image. -/
@[simp]
theorem chowFunctor_obj
    (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (i : ℤ) :
    (chowFunctor k i).obj M = chowGroup M i :=
  rfl

/-- Computation of the Chow-group functor on a motive morphism. -/
theorem chowFunctor_map_apply (i : ℤ)
    {M N : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)} (c : M ⟶ N)
    (alpha : chowGroup M i) :
    (((chowFunctor k i).map c).hom alpha).1 =
      ((chowRealization k i).map c.f).hom alpha.1 :=
  rfl

/-- The degree identity identifying a Tate corepresenter with the Chow degree. -/
theorem chowTate_degree (i m : ℤ) : i + m = m - -i := by
  ring

/-- The canonical linear identification of the Chow group with morphisms from the
Tate-twisted unit. -/
noncomputable def chowGroupEquivHom
    (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (i : ℤ) :
    chowGroup M i ≃ₗ[ℚ]
      (ChowMotive.tateTwist (SchemeOverField.point k) (-i) ⟶ M) where
  toFun alpha :=
    { f := castDegree (chowTate_degree i M.X.2)
        (cohomologyEquiv M.X.1.scheme (i + M.X.2) alpha.1)
      comm := by
        sorry }
  map_add' := by
    sorry
  map_smul' := by
    sorry
  invFun g :=
    ⟨(cohomologyEquiv M.X.1.scheme (i + M.X.2)).symm
      (castDegree (chowTate_degree i M.X.2).symm g.f), by
        sorry⟩
  left_inv := by
    sorry
  right_inv := by
    sorry

/-- The Chow-group functor is naturally linearly isomorphic to the linear coyoneda
functor represented by the Tate-twisted unit. -/
noncomputable def chowFunctorIsoCoyoneda (k : Type u) [Field k] (i : ℤ) :
    chowFunctor k i ≅
      (linearCoyoneda ℚ
        (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k))).obj
        (Opposite.op (ChowMotive.tateTwist (SchemeOverField.point k) (-i))) :=
  NatIso.ofComponents (fun M ↦ (chowGroupEquivHom M i).toModuleIso) (by
    sorry)

/-- The degree-`i` Chow-group functor is corepresented by the Tate-twisted unit. -/
noncomputable def chowRepresentedBy (k : Type u) [Field k] (i : ℤ) :
    ((chowFunctor k i) ⋙ forget (ModuleCat.{u + 1} ℚ)).CorepresentableBy
      (ChowMotive.tateTwist (SchemeOverField.point k) (-i)) :=
  (Functor.CorepresentableBy.coyoneda
    (Opposite.op (ChowMotive.tateTwist (SchemeOverField.point k) (-i)))).ofIso
      (Functor.isoWhiskerRight (chowFunctorIsoCoyoneda k i).symm
        (forget (ModuleCat.{u + 1} ℚ)))

/-- The underlying correspondence of the canonical Chow-class identification. -/
@[simp]
theorem chowGroupEquivHom_apply_f
    (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (i : ℤ)
    (y : chowGroup M i) :
    (chowGroupEquivHom M i y).f =
      castDegree (chowTate_degree i M.X.2)
        (cohomologyEquiv M.X.1.scheme (i + M.X.2) y.1) :=
  rfl

/-- The class underlying a morphism from the Tate-twisted unit. -/
@[simp]
theorem chowGroupEquivHom_symm_apply_coe
    (M : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) (i : ℤ)
    (g : ChowMotive.tateTwist (SchemeOverField.point k) (-i) ⟶ M) :
    ((chowGroupEquivHom M i).symm g).1 =
      (cohomologyEquiv M.X.1.scheme (i + M.X.2)).symm
        (castDegree (chowTate_degree i M.X.2).symm g.f) :=
  rfl

end ChowMotive
