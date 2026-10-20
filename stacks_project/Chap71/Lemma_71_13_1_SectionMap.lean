module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap71.Lemma_71_11_2_Functor
public import stacks_project.Chap71.Lemma_71_11_5_TwistAlgebra

/-!
# Invertible maps into relative Proj of algebraic spaces

A graded map from a pulled-back quasi-coherent algebra into the tensor powers of an
invertible module determines an open domain in the source, a morphism from that domain
into relative Proj, and a degreewise comparison of Serre twists with those powers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : X ⟶ Y)
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y)}
variable (deg : DegreePieces 𝒜) (L : X.Modules)

/-- A homomorphism of graded `𝒪_X`-algebras `f^* 𝒜 ⟶ ⊕_{n ≥ 0} L^{⊗ n}`, recorded by its
unlifted homogeneous components together with unit and multiplication laws. -/
structure GradedMapToPowers where
  /-- The degree-`n` component `f^* 𝒜_n ⟶ L^{⊗ n}`. -/
  hom :
    ∀ n : ℕ, (Modules.pullback f).obj (deg.obj n) ⟶ tensorPowerUnit L n
  /-- Degree zero sends the pulled-back unit of `𝒜` to the tensor-power unit. -/
  map_one :
    Modules.structureModulePullbackInv f ≫
        (Modules.pullback f).map (degreeZeroUnit deg) ≫ hom 0 =
      eqToHom (tensorPowerUnit_zero L).symm
  /-- Homogeneous multiplication is preserved. -/
  map_mul :
    ∀ i j : ℕ,
      pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
          (Modules.pullback f).map (deg.mul i j) ≫ hom (i + j) =
        tensorHom (hom i) (hom j) ≫ (tensorPowerUnitAddIso L i j).hom

namespace GradedMapToPowers

/-- Assemble a graded map into tensor powers from its homogeneous components and algebra
laws. -/
def of
    (hom :
      ∀ n : ℕ, (Modules.pullback f).obj (deg.obj n) ⟶ tensorPowerUnit L n)
    (map_one :
      Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map (degreeZeroUnit deg) ≫ hom 0 =
        eqToHom (tensorPowerUnit_zero L).symm)
    (map_mul :
      ∀ i j : ℕ,
        pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
            (Modules.pullback f).map (deg.mul i j) ≫ hom (i + j) =
          tensorHom (hom i) (hom j) ≫ (tensorPowerUnitAddIso L i j).hom) :
    GradedMapToPowers f deg L where
  hom := hom
  map_one := map_one
  map_mul := map_mul

/-- The unit and multiplication laws of a graded map into tensor powers hold
simultaneously. -/
theorem spec (ψ : GradedMapToPowers f deg L) :
    (Modules.structureModulePullbackInv f ≫
          (Modules.pullback f).map (degreeZeroUnit deg) ≫ ψ.hom 0 =
        eqToHom (tensorPowerUnit_zero L).symm) ∧
      ∀ i j : ℕ,
        pullbackTensorLax f (deg.obj i) (deg.obj j) ≫
            (Modules.pullback f).map (deg.mul i j) ≫ ψ.hom (i + j) =
          tensorHom (ψ.hom i) (ψ.hom j) ≫ (tensorPowerUnitAddIso L i j).hom :=
  sorry

/-- Two graded maps into tensor powers agree when every homogeneous component agrees. -/
theorem hom_ext (ψ ψ' : GradedMapToPowers f deg L)
    (h : ∀ n : ℕ, ψ.hom n = ψ'.hom n) : ψ = ψ' :=
  sorry

end GradedMapToPowers

variable {F : ProjFunctor Y 𝒜} (hF : F.IsAssociatedToQuadruples deg)
variable [isInvertibleObject L] (ψ : GradedMapToPowers f deg L)

/-- An open subspace `U(ψ) ⊂ X`, a morphism `r_{L,ψ} : U(ψ) ⟶ underline{Proj}_Y(𝒜)` over
`Y`, and a graded comparison `θ` from pulled-back Serre twists to the restricted tensor
powers of `L`. -/
structure SectionMap (ψ : GradedMapToPowers f deg L) where
  /-- The open subspace `U(ψ) ⊂ X` on which the morphism is defined. -/
  domain : OpenSubspace X
  /-- The morphism `r_{L,ψ} : U(ψ) ⟶ underline{Proj}_Y(𝒜)`. -/
  map : domain.X ⟶ toAlgebraicSpace F hF
  /-- The morphism lies over `Y`. -/
  map_over_base :
    map ≫ toAlgebraicSpace_hom F hF = domain.ι ≫ f
  /-- The degree-`n` comparison
  `r^* 𝒪(n) ⟶ L^{⊗ n}|_{U(ψ)}`. -/
  theta :
    ∀ n : ℕ,
      (Modules.pullback map).obj (CanonicalTwists.obj F hF (Int.ofNat n)) ⟶
        (Modules.pullback domain.ι).obj (tensorPowerUnit L n)
  /-- Degree zero of `θ` sends the pulled-back twist unit to the tensor-power unit. -/
  theta_map_one :
    (Modules.pullback map).map (CanonicalTwists.unit F hF) ≫ theta 0 =
      (pullbackMonoidalUnitIso map).hom ≫
        Modules.structureModulePullbackInv domain.ι ≫
          (Modules.pullback domain.ι).map (eqToHom (tensorPowerUnit_zero L).symm)
  /-- Homogeneous multiplication is preserved by `θ`. -/
  theta_map_mul :
    ∀ i j : ℕ,
      pullbackTensorLax map
            (CanonicalTwists.obj F hF (Int.ofNat i))
            (CanonicalTwists.obj F hF (Int.ofNat j)) ≫
          (Modules.pullback map).map
              (CanonicalTwists.mul F hF (Int.ofNat i) (Int.ofNat j)) ≫
            eqToHom
                (congrArg
                  (fun k : ℤ ↦
                    (Modules.pullback map).obj (CanonicalTwists.obj F hF k))
                  (Int.natCast_add i j).symm) ≫
              theta (i + j) =
        tensorHom (theta i) (theta j) ≫
          pullbackTensorLax domain.ι
              (tensorPowerUnit L i) (tensorPowerUnit L j) ≫
            (Modules.pullback domain.ι).map (tensorPowerUnitAddIso L i j).hom

namespace SectionMap

/-- Assemble a section map from its open domain, morphism over `Y`, and degreewise twist
comparison. -/
def of (domain : OpenSubspace X) (map : domain.X ⟶ toAlgebraicSpace F hF)
    (map_over_base :
      map ≫ toAlgebraicSpace_hom F hF = domain.ι ≫ f)
    (theta :
      ∀ n : ℕ,
        (Modules.pullback map).obj (CanonicalTwists.obj F hF (Int.ofNat n)) ⟶
          (Modules.pullback domain.ι).obj (tensorPowerUnit L n))
    (theta_map_one :
      (Modules.pullback map).map (CanonicalTwists.unit F hF) ≫ theta 0 =
        (pullbackMonoidalUnitIso map).hom ≫
          Modules.structureModulePullbackInv domain.ι ≫
            (Modules.pullback domain.ι).map (eqToHom (tensorPowerUnit_zero L).symm))
    (theta_map_mul :
      ∀ i j : ℕ,
        pullbackTensorLax map
              (CanonicalTwists.obj F hF (Int.ofNat i))
              (CanonicalTwists.obj F hF (Int.ofNat j)) ≫
            (Modules.pullback map).map
                (CanonicalTwists.mul F hF (Int.ofNat i) (Int.ofNat j)) ≫
              eqToHom
                  (congrArg
                    (fun k : ℤ ↦
                      (Modules.pullback map).obj (CanonicalTwists.obj F hF k))
                    (Int.natCast_add i j).symm) ≫
                theta (i + j) =
          tensorHom (theta i) (theta j) ≫
            pullbackTensorLax domain.ι
                (tensorPowerUnit L i) (tensorPowerUnit L j) ≫
              (Modules.pullback domain.ι).map (tensorPowerUnitAddIso L i j).hom) :
    SectionMap f deg L hF ψ where
  domain := domain
  map := map
  map_over_base := map_over_base
  theta := theta
  theta_map_one := theta_map_one
  theta_map_mul := theta_map_mul

/-- The underlying morphism of a section map, as a morphism over `Y`. -/
def overHom (c : SectionMap f deg L hF ψ) :
    Over.mk (c.domain.ι ≫ f) ⟶ Over.mk (toAlgebraicSpace_hom F hF) :=
  Over.homMk c.map c.map_over_base

/-- `overHom` is `Over.homMk` of the underlying morphism. -/
theorem overHom_eq (c : SectionMap f deg L hF ψ) :
    overHom f deg L hF ψ c = Over.homMk c.map c.map_over_base :=
  sorry

/-- A section map has an open-immersion domain inclusion and lies over `Y`. -/
theorem spec (c : SectionMap f deg L hF ψ) :
    IsOpenImmersion c.domain.ι ∧
      c.map ≫ toAlgebraicSpace_hom F hF = c.domain.ι ≫ f :=
  sorry

/-- The unit and multiplication laws of `c.theta` hold simultaneously. -/
theorem theta_spec (c : SectionMap f deg L hF ψ) :
    ((Modules.pullback c.map).map (CanonicalTwists.unit F hF) ≫ c.theta 0 =
        (pullbackMonoidalUnitIso c.map).hom ≫
          Modules.structureModulePullbackInv c.domain.ι ≫
            (Modules.pullback c.domain.ι).map
              (eqToHom (tensorPowerUnit_zero L).symm)) ∧
      ∀ i j : ℕ,
        pullbackTensorLax c.map
              (CanonicalTwists.obj F hF (Int.ofNat i))
              (CanonicalTwists.obj F hF (Int.ofNat j)) ≫
            (Modules.pullback c.map).map
                (CanonicalTwists.mul F hF (Int.ofNat i) (Int.ofNat j)) ≫
              eqToHom
                  (congrArg
                    (fun k : ℤ ↦
                      (Modules.pullback c.map).obj (CanonicalTwists.obj F hF k))
                    (Int.natCast_add i j).symm) ≫
                c.theta (i + j) =
          tensorHom (c.theta i) (c.theta j) ≫
            pullbackTensorLax c.domain.ι
                (tensorPowerUnit L i) (tensorPowerUnit L j) ≫
              (Modules.pullback c.domain.ι).map
                (tensorPowerUnitAddIso L i j).hom :=
  sorry

end SectionMap

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
