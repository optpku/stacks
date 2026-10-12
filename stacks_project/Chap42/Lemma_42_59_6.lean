/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_59_5
public import stacks_project.Chap42.Lemma_42_35_4_OpenRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom.VirtualNormalBundle

/-- Lemma 42.59.6 (1): in Situation 42.7.1, if `f : X ⟶ Y` and `g : Y ⟶ Z` are local complete
intersection morphisms of schemes locally of finite type over `S`, and the Gysin map exists
for `g ∘ f` (Lean `f ≫ g`) and for `g`, then the Gysin map exists for `f`. -/
@[stacks 0FF5]
theorem hasGysinMap_of_comp
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection g.left]
    (hfg : HasGysinMap (f ≫ g)) (hg : HasGysinMap g) : HasGysinMap f := sorry

/-- The underlying scheme morphism of a composite of LCI morphisms over `S` is LCI. -/
instance isLocalCompleteIntersection_over_comp
    {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection g.left] :
    LocallyOfType RingHom.IsLocalCompleteIntersection (f ≫ g).left := sorry

/-- The two paths `X ⟶ Y ⟶ Z` and `X ⟶ P ⟶ Z` agree on underlying scheme morphisms. -/
theorem gysinCompImmersion_comm
    {S : Scheme.{u}} {X Y Z P : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : X ⟶ P) (σ : P ⟶ Z) (hfac : i ≫ σ = f ≫ g) :
    f.left ≫ g.left = i.left ≫ σ.left := sorry

/-- The comparison `X ⟶ P ×_Z Y` respects the structure maps to `S`. -/
theorem gysinCompImmersion_over
    {S : Scheme.{u}} {X Y Z P : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : X ⟶ P) (σ : P ⟶ Z) (hfac : i ≫ σ = f ≫ g) :
    pullback.lift f.left i.left (gysinCompImmersion_comm f g i σ hfac) ≫
      (OpenRestriction.baseChange σ g).hom = X.hom := sorry

/-- The induced map `X ⟶ P ×_Z Y` of an immersion-smooth factorization of `g ∘ f`. -/
noncomputable def gysinCompImmersion
    {S : Scheme.{u}} {X Y Z P : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : X ⟶ P) (σ : P ⟶ Z) (hfac : i ≫ σ = f ≫ g) :
    X ⟶ OpenRestriction.baseChange σ g :=
  Over.homMk (pullback.lift f.left i.left (gysinCompImmersion_comm f g i σ hfac))
    (gysinCompImmersion_over f g i σ hfac)

/-- The induced maps `X ⟶ P ×_Z Y ⟶ Y` recover `f`. -/
theorem gysinCompImmersion_comp
    {S : Scheme.{u}} {X Y Z P : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : X ⟶ P) (σ : P ⟶ Z) (hfac : i ≫ σ = f ≫ g) :
    gysinCompImmersion f g i σ hfac ≫ OpenRestriction.baseChangeToTarget σ g = f := sorry

/-- The induced comparison `X ⟶ P ×_Z Y` is an immersion when `X ⟶ P` is. -/
instance gysinCompImmersion_isImmersion
    {S : Scheme.{u}} {X Y Z P : Over S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : X ⟶ P) (σ : P ⟶ Z) (hfac : i ≫ σ = f ≫ g)
    [IsImmersion i.left] :
    IsImmersion (gysinCompImmersion f g i σ hfac).left := sorry

/-- Integer grading identity comparing the composed Gysin degrees of `f` and `g` with the
Gysin degree of `g ∘ f`. -/
theorem gysin_comp_lci_degree (cf tf cg tg cfg tfg : ℕ)
    (hdim : (cf : ℤ) - tf + ((cg : ℤ) - tg) = (cfg : ℤ) - tfg) :
    (cf : ℤ) + (-(tf : ℤ)) + ((cg : ℤ) + (-(tg : ℤ))) = (cfg : ℤ) + (-(tfg : ℤ)) := sorry

/-- Lemma 42.59.6 (2): in Situation 42.7.1, if `f : X ⟶ Y` and `g : Y ⟶ Z` are local complete
intersection morphisms of schemes locally of finite type over `S`, then
`(g ∘ f)^! = f^! ∘ g^!`. Source `g ∘ f` is Lean `f ≫ g`, and `f^!` is
`bivariantGysinClassOfFactorization` of `globalClassOfRank` and `flatPullback` as in
Definition 42.59.4 and Lemma 42.59.5. -/
@[stacks 0FF5]
theorem gysin_comp_lci
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left]
    [LocallyOfType RingHom.IsLocalCompleteIntersection g.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (σ : P ⟶ Y) (hi : IsImmersion i.left)
    [IsClosedImmersion i.left] [IsRegularImmersion i.left]
    [hσ : Smooth σ.left] (hfac : i ≫ σ = f)
    (tf : ℕ) [Scheme.Hom.RelativeDimension σ.left tf]
    (cf : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank cf (Scheme.Hom.conormalSheaf i.left)]
    (ef : Scheme.Modules.dual (Scheme.Hom.normalSheaf i.left) ≅
      Scheme.Hom.conormalSheaf i.left)
    (Df : ClosedSpecialization δ X.hom P.hom i.left (Over.w i)
      (ofNormalSheaf i.left cf ef))
    {Q : Over S} [LocallyOfFiniteType Q.hom]
    (j : Y ⟶ Q) (τ : Q ⟶ Z) (hj : IsImmersion j.left)
    [IsClosedImmersion j.left] [IsRegularImmersion j.left]
    [hτ : Smooth τ.left] (hfacg : j ≫ τ = g)
    (tg : ℕ) [Scheme.Hom.RelativeDimension τ.left tg]
    (cg : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank cg (Scheme.Hom.conormalSheaf j.left)]
    (eg : Scheme.Modules.dual (Scheme.Hom.normalSheaf j.left) ≅
      Scheme.Hom.conormalSheaf j.left)
    (Dg : ClosedSpecialization δ Y.hom Q.hom j.left (Over.w j)
      (ofNormalSheaf j.left cg eg))
    {R : Over S} [LocallyOfFiniteType R.hom]
    (k : X ⟶ R) (ρ : R ⟶ Z) (hk : IsImmersion k.left)
    [IsClosedImmersion k.left] [IsRegularImmersion k.left]
    [hρ : Smooth ρ.left] (hfacfg : k ≫ ρ = f ≫ g)
    (tfg : ℕ) [Scheme.Hom.RelativeDimension ρ.left tfg]
    (cfg : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank cfg
      (Scheme.Hom.conormalSheaf k.left)]
    (efg : Scheme.Modules.dual (Scheme.Hom.normalSheaf k.left) ≅
      Scheme.Hom.conormalSheaf k.left)
    (Dfg : ClosedSpecialization δ X.hom R.hom k.left (Over.w k)
      (ofNormalSheaf k.left cfg efg))
    (hdim : (cf : ℤ) - tf + ((cg : ℤ) - tg) = (cfg : ℤ) - tfg) :
    bivariantGysinClassOfFactorization δ X Z (f ≫ g) R k ρ hk hρ hfacfg
        (overHom_eq_over k ▸
          globalClassOfRank δ X.hom R.hom k.left (Over.w k)
            (ofNormalSheaf k.left cfg efg) Dfg cfg)
        (flatPullback δ ρ tfg) =
      Nonnegative.castGrading δ (gysin_comp_lci_degree cf tf cg tg cfg tfg hdim)
        (comp δ f g
          (bivariantGysinClassOfFactorization δ X Y f P i σ hi hσ hfac
            (overHom_eq_over i ▸
              globalClassOfRank δ X.hom P.hom i.left (Over.w i)
                (ofNormalSheaf i.left cf ef) Df cf)
            (flatPullback δ σ tf))
          (bivariantGysinClassOfFactorization δ Y Z g Q j τ hj hτ hfacg
            (overHom_eq_over j ▸
              globalClassOfRank δ Y.hom Q.hom j.left (Over.w j)
                (ofNormalSheaf j.left cg eg) Dg cg)
            (flatPullback δ τ tg))) := sorry

end AlgebraicGeometry.BivariantClass
