/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap71.Lemma_71_11_2_Comparison
public import stacks_project.Chap71.Lemma_71_12_2_Map

/-!
# Étale restriction of relative projective-spectrum maps of algebraic spaces

A relative projective-spectrum map over an algebraic space restricts along a
scheme morphism `g : W ⟶ X` to an open of `Q ×_X W`, a morphism to `P ×_X W`,
and degreewise twist comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite
open scoped ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProjMap

variable {S : Scheme.{u}} {X P Q : AlgebraicSpace S}
variable {πP : P ⟶ X} {πQ : Q ⟶ X}
variable {𝒜 ℬ : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent]
variable {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules}
variable {φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ}

/-- The open subspace `U(ψ) ×_X W ⊂ Q ×_X W`, realized as the pullback of
`U(ψ) ⟶ Q` along `Q ×_X W ⟶ Q`. -/
def restrictDomain (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    {W : Over S} (g : ofOver W ⟶ X) : OpenSubspace (pullback πQ g) :=
  OpenSubspace.ofι (pullback.snd r.domain.ι (pullback.fst πQ g))

/-- The restricted morphism `r_ψ|_{U(ψ) ×_X W} : U(ψ) ×_X W ⟶ P ×_X W`. -/
def restrictMap (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    {W : Over S} (g : ofOver W ⟶ X) :
    (restrictDomain r g).X ⟶ pullback πP g :=
  pullback.lift
    (pullback.fst r.domain.ι (pullback.fst πQ g) ≫ r.map)
    (pullback.snd r.domain.ι (pullback.fst πQ g) ≫ pullback.snd πQ g)
    ((Category.assoc _ _ _).trans
    ((congrArg (fun f ↦ pullback.fst r.domain.ι (pullback.fst πQ g) ≫ f)
        r.map_over_base).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ f ≫ πQ)
            (@pullback.condition _ _ _ _ _ r.domain.ι (pullback.fst πQ g) _)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f ↦
                pullback.snd r.domain.ι (pullback.fst πQ g) ≫ f)
                (@pullback.condition _ _ _ _ _ πQ g _)).trans
              (Category.assoc _ _ _).symm))))))

/-- The degreewise twist comparison `θ_ψ` pulled back to `U(ψ) ×_X W`. -/
def restrictTheta (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    {W : Over S} (g : ofOver W ⟶ X) (n : ℤ) :
    (Modules.pullback (restrictMap r g)).obj
        ((Modules.pullback (pullback.fst πP g)).obj (twistP n)) ⟶
      (Modules.pullback (restrictDomain r g).ι).obj
        ((Modules.pullback (pullback.fst πQ g)).obj (twistQ n)) :=
  let fst := pullback.fst r.domain.ι (pullback.fst πQ g)
  let hCart := IsPullback.of_hasPullback r.domain.ι (pullback.fst πQ g)
  (Modules.pullbackCompIso (restrictMap r g) (pullback.fst πP g)).hom.app (twistP n) ≫
    eqToHom
      (congrArg (fun f ↦ (Modules.pullback f).obj (twistP n))
        (pullback.lift_fst
          (fst ≫ r.map)
          (pullback.snd r.domain.ι (pullback.fst πQ g) ≫ pullback.snd πQ g)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f ↦ pullback.fst r.domain.ι (pullback.fst πQ g) ≫ f)
                r.map_over_base).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun f ↦ f ≫ πQ)
                    (@pullback.condition _ _ _ _ _
                      r.domain.ι (pullback.fst πQ g) _)).trans
                  ((Category.assoc _ _ _).trans
                    ((congrArg (fun f ↦
                        pullback.snd r.domain.ι (pullback.fst πQ g) ≫ f)
                        (@pullback.condition _ _ _ _ _ πQ g _)).trans
                      (Category.assoc _ _ _).symm)))))))) ≫
    (Modules.pullbackCompIso fst r.map).inv.app (twistP n) ≫
    (Modules.pullback fst).map (r.theta n) ≫
    (Modules.pullbackCompIso
          (pullback.snd r.domain.ι (pullback.fst πQ g)) (pullback.fst πQ g) ≪≫
        eqToIso (congrArg Modules.pullback hCart.w.symm) ≪≫
        (Modules.pullbackCompIso fst r.domain.ι).symm).inv.app (twistQ n)

/-- The inclusion of `U(ψ) ×_X W` is the pullback of `U(ψ) ⟶ Q`. -/
theorem restrictDomain_ι (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    {W : Over S} (g : ofOver W ⟶ X) :
    (restrictDomain r g).ι = pullback.snd r.domain.ι (pullback.fst πQ g) :=
  sorry

/-- The restricted open is the fibre product of `U(ψ) ⟶ Q` with `Q ×_X W ⟶ Q`. -/
theorem restrictDomain_spec (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    {W : Over S} (g : ofOver W ⟶ X) :
    (restrictDomain r g).X =
        pullback r.domain.ι (pullback.fst πQ g) ∧
      (restrictDomain r g).ι = pullback.snd r.domain.ι (pullback.fst πQ g) :=
  sorry

/-- The two projections of `U(ψ) ×_X W` agree over `X`. -/
theorem restrictMap_condition (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    {W : Over S} (g : ofOver W ⟶ X) :
    (pullback.fst r.domain.ι (pullback.fst πQ g) ≫ r.map) ≫ πP =
      (pullback.snd r.domain.ι (pullback.fst πQ g) ≫ pullback.snd πQ g) ≫ g :=
  sorry

/-- The restricted morphism commutes with the structural morphisms to `W`. -/
theorem restrictMap_over_base (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    {W : Over S} (g : ofOver W ⟶ X) :
    restrictMap r g ≫ pullback.snd πP g =
      (restrictDomain r g).ι ≫ pullback.snd πQ g :=
  sorry

/-- The first projection of the restricted morphism recovers `r_ψ` on `U(ψ)`. -/
theorem restrictMap_fst (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    {W : Over S} (g : ofOver W ⟶ X) :
    restrictMap r g ≫ pullback.fst πP g =
      pullback.fst r.domain.ι (pullback.fst πQ g) ≫ r.map :=
  sorry

/-- The unlifted nonnegative component of a map of quasi-coherent graded
`𝒪_X`-algebras, recovered from the universe-lifted degreewise map along the
degree-piece identifications. -/
def pullbackHomDegree (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (degA : DegreePieces 𝒜) (degB : DegreePieces ℬ) (n : ℕ) :
    degA.obj n ⟶ degB.obj n :=
  Modules.unliftModuleHom
    ((degA.iso n).hom ≫ φ.hom (Int.ofNat n) ≫ (degB.iso n).inv)

/-- Universe lift of `pullbackHomDegree` recovers the given degreewise map. -/
theorem pullbackHomDegree_spec (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (degA : DegreePieces 𝒜) (degB : DegreePieces ℬ) (n : ℕ) :
    Modules.liftModuleMap (pullbackHomDegree φ degA degB n) =
      (degA.iso n).hom ≫ φ.hom (Int.ofNat n) ≫ (degB.iso n).inv :=
  sorry

/-- The nonnegative degree-`n` component of `ψ|_W`, as a map of pulled-back
degree pieces on `W`. -/
def pullbackHomOfNat (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    {W : Over S} (g : ofOver W ⟶ X)
    (degA : DegreePieces 𝒜) (degB : DegreePieces ℬ) (n : ℕ) :
    pullbackDegree g degA n ⟶ pullbackDegree g degB n :=
  (Modules.restrictToScheme W).map
    ((Modules.pullback g).map (pullbackHomDegree φ degA degB n))

/-- `pullbackHomOfNat` is restriction of the pulled-back unlifted component. -/
theorem pullbackHomOfNat_eq (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    {W : Over S} (g : ofOver W ⟶ X)
    (degA : DegreePieces 𝒜) (degB : DegreePieces ℬ) (n : ℕ) :
    pullbackHomOfNat φ g degA degB n =
      (Modules.restrictToScheme W).map
        ((Modules.pullback g).map (pullbackHomDegree φ degA degB n)) :=
  rfl

/-- Negative components of `g^* 𝒜` are the zero module. -/
theorem pullbackAlgebra_obj_negSucc {W : Over S} (g : ofOver W ⟶ X)
    (deg : DegreePieces 𝒜) (n : ℕ) :
    (pullbackAlgebra g deg).obj (Int.negSucc n) = 0 :=
  pullbackAlgebraObj_negSucc g deg n

/-- The degreewise components of `ψ|_W`. -/
def pullbackHomObj (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    {W : Over S} (g : ofOver W ⟶ X)
    (degA : DegreePieces 𝒜) (degB : DegreePieces ℬ) (n : ℤ) :
    (pullbackAlgebra g degA).obj n ⟶ (pullbackAlgebra g degB).obj n :=
  match n with
  | Int.ofNat k =>
      eqToHom (pullbackAlgebra_obj_ofNat g degA k).symm ≫
        pullbackHomOfNat φ g degA degB k ≫
        eqToHom (pullbackAlgebra_obj_ofNat g degB k)
  | Int.negSucc k =>
      eqToHom (pullbackAlgebra_obj_negSucc g degA k).symm ≫
        (0 : (0 : W.left.Modules) ⟶ (0 : W.left.Modules)) ≫
        eqToHom (pullbackAlgebra_obj_negSucc g degB k)

/-- Nonnegative components of `pullbackHomObj` are `pullbackHomOfNat` after the
degree-piece identifications. -/
theorem pullbackHomObj_ofNat (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    {W : Over S} (g : ofOver W ⟶ X)
    (degA : DegreePieces 𝒜) (degB : DegreePieces ℬ) (n : ℕ) :
    pullbackHomObj φ g degA degB (Int.ofNat n) =
      eqToHom (pullbackAlgebra_obj_ofNat g degA n).symm ≫
        pullbackHomOfNat φ g degA degB n ≫
        eqToHom (pullbackAlgebra_obj_ofNat g degB n) :=
  rfl

/-- The pulled-back graded algebra map `ψ|_W : g^* 𝒜 ⟶ g^* ℬ`. -/
def pullbackHom (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    {W : Over S} (g : ofOver W ⟶ X)
    (degA : DegreePieces 𝒜) (degB : DegreePieces ℬ) :
    GradedAlgebraSheaf.Hom.{u, u} (pullbackAlgebra g degA) (pullbackAlgebra g degB) where
  hom := pullbackHomObj φ g degA degB
  map_one := sorry
  map_mul := sorry

/-- The degreewise components of `pullbackHom` are `pullbackHomObj`. -/
theorem pullbackHom_apply (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    {W : Over S} (g : ofOver W ⟶ X)
    (degA : DegreePieces 𝒜) (degB : DegreePieces ℬ) (n : ℤ) :
    (pullbackHom φ g degA degB).hom n = pullbackHomObj φ g degA degB n :=
  rfl

/-- On nonnegative degrees, `pullbackHom` is restriction of the pulled-back
unlifted component of `φ`. -/
theorem pullbackHom_spec (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    {W : Over S} (g : ofOver W ⟶ X)
    (degA : DegreePieces 𝒜) (degB : DegreePieces ℬ) (n : ℕ) :
    (pullbackHom φ g degA degB).hom (Int.ofNat n) =
      eqToHom (pullbackAlgebra_obj_ofNat g degA n).symm ≫
        pullbackHomOfNat φ g degA degB n ≫
        eqToHom (pullbackAlgebra_obj_ofNat g degB n) :=
  sorry

/-- The restricted degreewise comparison is the pullback of `r.theta n` along
`U(ψ) ×_Q (Q ×_X W) ⟶ U(ψ)`. -/
theorem restrictTheta_spec (r : RelativeProjMap πP πQ 𝒜 ℬ twistP twistQ φ)
    {W : Over S} (g : ofOver W ⟶ X) (n : ℤ) :
    restrictTheta r g n =
      (Modules.pullbackCompIso (restrictMap r g) (pullback.fst πP g)).hom.app
          (twistP n) ≫
        eqToHom
          (congrArg (fun f ↦ (Modules.pullback f).obj (twistP n))
            (restrictMap_fst r g)) ≫
        (Modules.pullbackCompIso
            (pullback.fst r.domain.ι (pullback.fst πQ g)) r.map).inv.app
          (twistP n) ≫
        (Modules.pullback
            (pullback.fst r.domain.ι (pullback.fst πQ g))).map (r.theta n) ≫
        (Modules.pullbackCompIso
              (pullback.snd r.domain.ι (pullback.fst πQ g))
              (pullback.fst πQ g) ≪≫
            eqToIso
              (congrArg Modules.pullback
                (@pullback.condition _ _ _ _ _
                  r.domain.ι (pullback.fst πQ g) _).symm) ≪≫
            (Modules.pullbackCompIso
                (pullback.fst r.domain.ι (pullback.fst πQ g))
                r.domain.ι).symm).inv.app (twistQ n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProjMap
