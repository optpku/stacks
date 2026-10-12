/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap106.Definition_106_3_3_FirstOrderThickening
public import stacks_project.Chap106.Lemma_106_6_7
public import stacks_project.Chap106.«106_6_8_1_Comparison»
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Inertia algebraic space and Hom-parameter module of a lift

For a first-order thickening of algebraic stacks, the inertia space of a lift
`ξ` of Remark 106.6.1 is the algebraic space representing `U' ×_{X'} U'`. Its
diagonal and source projection present the infinitesimal automorphism sheaf of
`ξ` as the internal Hom `Hom_{O_U}(Δ^* Ω_{I/U}, C_{U/U'})`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open Limits Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}} {X X' : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack X']
variable (iX : X ⟶ X') [IsThickening iX]
variable {W : AlgebraicSpace S} (x : W.toGroupoids ⟶ X)
variable [Groupoids.Hom.Smooth x]

namespace Object

/-- The structure morphism of a lift is étale. -/
instance instEtale (ξ : Object iX x) : AlgebraicSpace.Etale ξ.a :=
  ξ.etale

/-- The morphism `i : U ⟶ U'` of a lift along a first-order thickening of
algebraic stacks is a first-order thickening of algebraic spaces. -/
instance instIsFirstOrderThickening (ξ : Object iX x)
    [IsFirstOrderThickening iX] :
    AlgebraicSpace.IsFirstOrderThickening ξ.i :=
  sorry

/-- The kernel pair of `ξ.x'` is representable by an algebraic space. -/
theorem inertia_isRepresentable (ξ : Object iX x) :
    IsRepresentableByAlgebraicSpace (kernelPair ξ.x') :=
  kernelPair_isRepresentableByAlgebraicSpace ξ.x'
    (IsRepresentableByAlgebraicSpace.of_toGroupoids ξ.U')

/-- The inertia algebraic space `I' = U' ×_{x', X', x'} U'` of a lift. -/
def inertia (ξ : Object iX x) : AlgebraicSpace S :=
  representingSpace (inertia_isRepresentable iX x ξ)

/-- `inertia ξ` is the chosen algebraic space representing the kernel pair of
`ξ.x'`. -/
theorem inertia_eq (ξ : Object iX x) :
    inertia iX x ξ = representingSpace (inertia_isRepresentable iX x ξ) :=
  rfl

/-- The bicategorical equivalence from the kernel pair of `ξ.x'` to the
groupoid fibration of `inertia ξ`. -/
def inertiaEquiv (ξ : Object iX x) :
    kernelPair ξ.x' ≌ (inertia iX x ξ).toGroupoids :=
  representingEquiv (inertia_isRepresentable iX x ξ)

/-- The source projection `p' : I' ⟶ U'` of the inertia space. -/
def inertiaSrc (ξ : Object iX x) : inertia iX x ξ ⟶ ξ.U' :=
  groupoidSource ξ.x' (Bicategory.Equivalence.id _) (inertiaEquiv iX x ξ)

/-- The target projection `q' : I' ⟶ U'` of the inertia space. -/
def inertiaTgt (ξ : Object iX x) : inertia iX x ξ ⟶ ξ.U' :=
  groupoidTarget ξ.x' (Bicategory.Equivalence.id _) (inertiaEquiv iX x ξ)

/-- The diagonal morphism `Δ' : U' ⟶ I'` of the inertia space. -/
def inertiaDiagonal (ξ : Object iX x) : ξ.U' ⟶ inertia iX x ξ :=
  groupoidIdentity ξ.x' (Bicategory.Equivalence.id _) (inertiaEquiv iX x ξ)

/-- The source projection of inertia is the groupoid source recovered from
`pr1`. -/
theorem inertiaSrc_eq (ξ : Object iX x) :
    inertiaSrc iX x ξ =
      groupoidSource ξ.x' (Bicategory.Equivalence.id _) (inertiaEquiv iX x ξ) :=
  rfl

/-- The target projection of inertia is the groupoid target recovered from
`pr0`. -/
theorem inertiaTgt_eq (ξ : Object iX x) :
    inertiaTgt iX x ξ =
      groupoidTarget ξ.x' (Bicategory.Equivalence.id _) (inertiaEquiv iX x ξ) :=
  rfl

/-- The inertia diagonal is the groupoid identity recovered from the identity
cone on `ξ.x'`. -/
theorem inertiaDiagonal_eq (ξ : Object iX x) :
    inertiaDiagonal iX x ξ =
      groupoidIdentity ξ.x' (Bicategory.Equivalence.id _) (inertiaEquiv iX x ξ) :=
  rfl

/-- The source projection splits the inertia diagonal. -/
theorem inertiaDiagonal_comp_src (ξ : Object iX x) :
    inertiaDiagonal iX x ξ ≫ inertiaSrc iX x ξ = 𝟙 ξ.U' :=
  sorry

/-- The target projection splits the inertia diagonal. -/
theorem inertiaDiagonal_comp_tgt (ξ : Object iX x) :
    inertiaDiagonal iX x ξ ≫ inertiaTgt iX x ξ = 𝟙 ξ.U' :=
  sorry

/-- The base change `I = U ×_{U'} I'` of inertia along `ξ.i`. -/
def inertiaSpace (ξ : Object iX x) : AlgebraicSpace S :=
  pullback ξ.i (inertiaSrc iX x ξ)

/-- `inertiaSpace ξ` is the fibre product of `ξ.i` with the inertia source. -/
theorem inertiaSpace_eq (ξ : Object iX x) :
    inertiaSpace iX x ξ = pullback ξ.i (inertiaSrc iX x ξ) :=
  rfl

/-- The projection `p : I ⟶ U` of the base-changed inertia. -/
def inertiaHom (ξ : Object iX x) : inertiaSpace iX x ξ ⟶ ξ.U :=
  pullback.fst ξ.i (inertiaSrc iX x ξ)

/-- The first-order thickening `I ⟶ I'` of the base-changed inertia. -/
def inertiaThickening (ξ : Object iX x) : inertiaSpace iX x ξ ⟶ inertia iX x ξ :=
  pullback.snd ξ.i (inertiaSrc iX x ξ)

/-- The diagonal `Δ : U ⟶ I` of the base-changed inertia. -/
def inertiaRestrict (ξ : Object iX x) : ξ.U ⟶ inertiaSpace iX x ξ :=
  pullback.lift (𝟙 ξ.U) (ξ.i ≫ inertiaDiagonal iX x ξ) sorry

/-- `inertiaHom ξ` is the first projection of the inertia pullback. -/
theorem inertiaHom_eq (ξ : Object iX x) :
    inertiaHom iX x ξ = pullback.fst ξ.i (inertiaSrc iX x ξ) :=
  rfl

/-- `inertiaThickening ξ` is the second projection of the inertia pullback. -/
theorem inertiaThickening_eq (ξ : Object iX x) :
    inertiaThickening iX x ξ = pullback.snd ξ.i (inertiaSrc iX x ξ) :=
  rfl

/-- The base-changed diagonal projects to the identity of `U`. -/
theorem inertiaRestrict_comp_hom (ξ : Object iX x) :
    inertiaRestrict iX x ξ ≫ inertiaHom iX x ξ = 𝟙 ξ.U :=
  sorry

/-- The base-changed diagonal is the restriction of `Δ'` along `ξ.i`. -/
theorem inertiaRestrict_comp_thickening (ξ : Object iX x) :
    inertiaRestrict iX x ξ ≫ inertiaThickening iX x ξ =
      ξ.i ≫ inertiaDiagonal iX x ξ :=
  sorry

/-- The thickening `I ⟶ I'` of base-changed inertia is first-order. -/
instance instInertiaThickeningIsFirstOrder (ξ : Object iX x)
    [IsFirstOrderThickening iX] :
    AlgebraicSpace.IsFirstOrderThickening (inertiaThickening iX x ξ) :=
  sorry

/-- The infinitesimal parameter module `Hom_{O_U}(Δ^* Ω_{I/U}, C_{U/U'})` of a
lift. -/
def parameterModule (ξ : Object iX x) [IsFirstOrderThickening iX] :
    RingedSite.ModuleCat.{u + 1} (AlgebraicSpace.commRingedSiteLift ξ.U) :=
  AlgebraicSpace.Hom.Deformation.parameterModule ξ.i (inertiaHom iX x ξ)
    (inertiaRestrict iX x ξ)

/-- `parameterModule ξ` is the ringed-site internal Hom of `Δ^* Ω_{I/U}` with
`C_{U/U'}`. -/
theorem parameterModule_eq (ξ : Object iX x) [IsFirstOrderThickening iX] :
    parameterModule iX x ξ =
      AlgebraicSpace.Hom.Deformation.parameterModule ξ.i (inertiaHom iX x ξ)
        (inertiaRestrict iX x ξ) :=
  rfl

/-- The Hom-parameter module of a first-order lift is quasi-coherent. -/
instance parameterModule_isQuasicoherent (ξ : Object iX x)
    [IsFirstOrderThickening iX] :
    (parameterModule iX x ξ).IsQuasicoherent :=
  sorry

/-- The base-changed inertia square `I = U ×_{U'} I'` is a pullback. -/
theorem inertiaHom_isPullback (ξ : Object iX x) :
    IsPullback (inertiaHom iX x ξ) (inertiaThickening iX x ξ) ξ.i
      (inertiaSrc iX x ξ) :=
  sorry

/-- The inertia diagonal square `U → I → I'`, `U → U' → I'` is a pullback. -/
theorem inertiaRestrict_isPullback (ξ : Object iX x) :
    IsPullback (inertiaRestrict iX x ξ) ξ.i (inertiaThickening iX x ξ)
      (inertiaDiagonal iX x ξ) :=
  sorry

/-- 0CKH for a lift: the Hom-parameter Type sheaf of `ξ` is isomorphic to the
deformation sheaf `autSheaf` of the inertia diagram. -/
theorem parameter_iso_aut (ξ : Object iX x) [IsFirstOrderThickening iX] :
    IsIsomorphic
      (AlgebraicSpace.Hom.Deformation.parameterSheafEtale ξ.i
        (inertiaHom iX x ξ) (inertiaRestrict iX x ξ))
      (AlgebraicSpace.Hom.Deformation.autSheaf ξ.i (inertiaThickening iX x ξ)
        (inertiaSrc iX x ξ) (inertiaDiagonal iX x ξ) (inertiaRestrict iX x ξ)
        (inertiaRestrict_isPullback iX x ξ)) :=
  sorry

end Object

end AlgebraicGeometry.AlgebraicStack.Lift
