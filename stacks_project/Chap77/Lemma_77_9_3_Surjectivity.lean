module

public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_15_2
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap77.«77_7_1_1_BaseChange»

/-!
# Surjectivity open of a module morphism

The open subspace of `B` complementary to the image of the support of `coker u`
under `|f|`, representing the flattening functor `F_surj` of Situation 77.7.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)

/-- The set of points of `|B|` complementary to `|f|(Supp(coker u))`. -/
def surjectivityLocus : Set (Points B) :=
  (Points.map f '' moduleSupport (cokernel u))ᶜ

/-- `surjectivityLocus f u` is the complement of the image of `moduleSupport (cokernel u)`
under `Points.map f`. -/
theorem surjectivityLocus_eq :
    surjectivityLocus f u = (Points.map f '' moduleSupport (cokernel u))ᶜ :=
  sorry

/-- The complement of `|f|(Supp(coker u))` is open when `𝒢` is of finite type and the
scheme-theoretic support of `𝒢` is proper over `B`. -/
theorem isOpen_surjectivityLocus [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    IsOpen (surjectivityLocus f u) :=
  sorry

/-- The open of `|B|` complementary to `|f|(Supp(coker u))`. -/
def surjectivityOpens [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    Opens (Points B) :=
  Opens.mk (surjectivityLocus f u) (isOpen_surjectivityLocus f u)

/-- The open subspace of `B` representing `F_surj`, cut out by
`surjectivityOpens f u`. -/
def surjectivityOpenSubspace [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    OpenSubspace B :=
  OpenSubspace.ofOpens (surjectivityOpens f u)

/-- The underlying point-set of `surjectivityOpenSubspace f u` is
`surjectivityLocus f u`. -/
theorem surjectivityOpenSubspace_pointsSet [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    (surjectivityOpenSubspace f u).pointsSet = surjectivityLocus f u :=
  sorry

/-- A test morphism `a : ofOver T ⟶ B` lands in `surjectivityLocus f u` if and only if
`baseChangeMap f a u` is an epimorphism. -/
theorem mem_surjectivityLocus_iff [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] {T : Over S} (a : ofOver T ⟶ B) :
    Set.range (Points.map a) ⊆ surjectivityLocus f u ↔
      Epi (baseChangeMap f a u) :=
  sorry

/-- The inclusion of `surjectivityOpenSubspace f u` into `B` is an open immersion. -/
instance instIsOpenImmersion_surjectivityOpenSubspace_ι [𝒢.IsFiniteType]
    [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)] :
    IsOpenImmersion (surjectivityOpenSubspace f u).ι :=
  (surjectivityOpenSubspace f u).isOpenImmersion

end AlgebraicGeometry.AlgebraicSpace.Modules
