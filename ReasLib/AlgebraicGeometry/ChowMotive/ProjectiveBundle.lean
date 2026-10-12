/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.ChowMotive.Additive
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Correspondence
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace ChowMotive.ProjectiveBundle

variable {k : Type u} [Field k]
variable (X P : Correspondence.Category k) (E : X.scheme.left.Modules)
variable (p : P.scheme ⟶ X.scheme)
variable (hp : Scheme.ProjectiveBundle.Representation p.left E)

/-- The `i`th power of the first Chern class of the tautological module pulled back to `X ⨯ P`. -/
noncomputable def chernPower (i : ℕ) :
    ChowCohomology.degree (fun _ ↦ 0) (X.scheme ⨯ P.scheme).hom (i : ℤ) :=
  (nsmul_one i : i • (1 : ℤ) = (i : ℤ)) ▸
    GradedMonoid.GMonoid.gnpow i
      (@ChowCohomology.firstChernClass _ _ (fun _ ↦ 0)
        (X.scheme ⨯ P.scheme).hom inferInstance inferInstance inferInstance
        ((Scheme.Modules.pullback
          (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
          (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp))
        (Scheme.Modules.Invertible.pullback
          (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme).left
          (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible p.left hp)))

/-- The zeroth tautological Chern power is the identity operational class. -/
theorem chernPower_zero :
    chernPower X P E p hp 0 =
      ChowCohomology.one (fun _ ↦ 0) (X.scheme ⨯ P.scheme).hom := sorry

/-- A successor tautological Chern power is obtained by one further product with
the pulled-back first Chern class. -/
theorem chernPower_succ (i : ℕ) :
    (GradedMonoid.mk (i + 1 : ℕ) (chernPower X P E p hp (i + 1)) :
      GradedMonoid (ChowCohomology.degree (fun _ ↦ 0) (X.scheme ⨯ P.scheme).hom)) =
      GradedMonoid.mk (i : ℤ) (chernPower X P E p hp i) *
        GradedMonoid.mk 1
          (@ChowCohomology.firstChernClass _ _ (fun _ ↦ 0)
            (X.scheme ⨯ P.scheme).hom inferInstance inferInstance inferInstance
            ((Scheme.Modules.pullback
              (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme).left).obj
              (Scheme.ProjectiveBundle.tautologicalSheaf p.left hp))
            (Scheme.Modules.Invertible.pullback
              (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme).left
              (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible p.left hp))) := sorry

/-- The integral correspondence obtained by capping the graph of `p` with the
`i`th tautological Chern power. -/
noncomputable def integralComponent (i : ℕ) :
    Correspondence.Integral X.scheme P.scheme (i : ℤ) :=
  Correspondence.castHom
    (Category.id_comp (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme)) (i : ℤ)
    ((add_zero (i : ℤ)) ▸
      BivariantClass.comp (fun _ ↦ 0) (𝟙 (X.scheme ⨯ P.scheme))
        (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme)
        (chernPower X P E p hp i)
        (@Correspondence.integralGraph k _ X.scheme P.scheme inferInstance inferInstance
          (inferInstance : IsSeparated X.scheme.hom) p))

/-- The integral component is the tautological Chern power capped with the graph class of `p`. -/
theorem integralComponent_def (i : ℕ) :
    integralComponent X P E p hp i =
      Correspondence.castHom
        (Category.id_comp (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme)) (i : ℤ)
        ((add_zero (i : ℤ)) ▸
          BivariantClass.comp (fun _ ↦ 0) (𝟙 (X.scheme ⨯ P.scheme))
            (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme)
            (chernPower X P E p hp i)
            (@Correspondence.integralGraph k _ X.scheme P.scheme inferInstance inferInstance
              (inferInstance : IsSeparated X.scheme.hom) p)) := sorry

/-- The rational correspondence given by rationalizing the integral tautological Chern-power
graph class. -/
noncomputable def chernGraphCorrespondence (i : ℕ) :
    Correspondence.Rational X.scheme P.scheme (i : ℤ) :=
  BivariantClass.rationalize (fun _ ↦ 0)
    (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme) (i : ℤ)
    (integralComponent X P E p hp i)

/-- The `i`th rational component is the scalar extension of its integral class. -/
theorem chernGraphCorrespondence_def (i : ℕ) :
    chernGraphCorrespondence X P E p hp i =
      BivariantClass.rationalize (fun _ ↦ 0)
        (Limits.prod.snd : X.scheme ⨯ P.scheme ⟶ P.scheme) (i : ℤ)
        (integralComponent X P E p hp i) := sorry

/-- The rational component satisfies the Karoubi compatibility required for a
morphism `h(X)(-i) ⟶ h(P)`. -/
theorem component_comm (i : ℕ) :
    let f : (ChowMotive.tateTwist X.scheme (-(i : ℤ))).X ⟶ (ChowMotive.h P.scheme).X :=
      Correspondence.castDegree
        ((zero_sub (-(i : ℤ))).trans (neg_neg (i : ℤ))).symm
        (chernGraphCorrespondence X P E p hp i)
    (ChowMotive.tateTwist X.scheme (-(i : ℤ))).p ≫ f ≫ (ChowMotive.h P.scheme).p = f := sorry

/-- The `i`th Chern-graph correspondence as a morphism from `h(X)(-i)` to `h(P)`. -/
noncomputable def component (i : ℕ) :
    ChowMotive.tateTwist X.scheme (-(i : ℤ)) ⟶ ChowMotive.h P.scheme where
  f := Correspondence.castDegree
    ((zero_sub (-(i : ℤ))).trans (neg_neg (i : ℤ))).symm
    (chernGraphCorrespondence X P E p hp i)
  comm := component_comm X P E p hp i

/-- The underlying graded correspondence of `component` is the degree transport of the
rational Chern-graph class. -/
theorem component_f (i : ℕ) :
    (component X P E p hp i).f =
      Correspondence.castDegree
        ((zero_sub (-(i : ℤ))).trans (neg_neg (i : ℤ))).symm
        (chernGraphCorrespondence X P E p hp i) := sorry

/-- The projective-bundle formula morphism, assembled from its Chern-graph components by the
finite categorical biproduct. -/
noncomputable def formulaMap (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] :
    (⨁ fun i : Fin r ↦ ChowMotive.tateTwist X.scheme (-(i : ℤ))) ⟶ ChowMotive.h P.scheme :=
  biproduct.desc fun i ↦ component X P E p hp i

/-- Restricting `formulaMap` to its `i`th biproduct summand gives the corresponding
Chern-graph component. -/
theorem formulaMap_ι (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin r) :
    biproduct.ι (fun j : Fin r ↦ ChowMotive.tateTwist X.scheme (-(j : ℤ))) i ≫
        formulaMap X P E p hp r = component X P E p hp i := sorry

/-- The projective-bundle formula morphism is an isomorphism in the category of Chow motives. -/
theorem formulaMap_isIso (X P : Correspondence.Category k)
    (E : Scheme.Modules X.scheme.left) (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (p : P.scheme ⟶ X.scheme)
    (hp : Scheme.ProjectiveBundle.Representation p.left E) :
    IsIso (formulaMap X P E p hp r) := sorry

end ChowMotive.ProjectiveBundle
