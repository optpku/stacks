/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import stacks_project.Chap66.«66_26_0_1_Pushforward»

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import stacks_project.Chap76.Lemma_76_7_6_Differentials

/-!
# Pullback comparison for relative differentials of algebraic spaces

A commutative square of algebraic spaces makes the composite of `f^♯` with the pushed
universal derivation into a `Y`-derivation.  Universality of `Ω_{X/Y}` and the
pullback–pushforward adjunction of `ringedToposHom f` produce the canonical comparison
`c_f : f^* Ω_{X/Y} ⟶ Ω_{X'/Y'}`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry ConcreteCategory
open AlgebraicGeometry.AlgebraicSpace
open PresheafOfModules.DifferentialsConstruction
open Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}}

/-- The underlying type-valued map of the universal derivation `d_{X/Y}`. -/
def universalDerivation_typeHom {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj (structureSheaf X) ⟶
      (ToInternal.underlying (structureSheaf X)).obj (relativeDifferentials h) :=
  InducedCategory.homMk
    { app := fun U ↦ ↾fun t ↦ (universalDerivation h).d (cast rfl t)
      naturality := fun _ _ _ ↦ sorry }

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

variable {S : Scheme.{u}}

/-- The type-valued composite of `f^♯` with the pushed universal derivation
`f_* d_{X'/Y'}`. -/
def comparisonSectionTypeHom
    {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y') :
    (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj (structureSheaf X) ⟶
      (ringedToposHom f).toTopos.pushforward.obj
        ((ToInternal.underlying (structureSheaf X')).obj (relativeDifferentials h')) :=
  (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).map (structureSheafMap f) ≫
    (ringPushforwardForgetIso f).hom.app (structureSheaf X') ≫
      (ringedToposHom f).toTopos.pushforward.map (universalDerivation_typeHom h')

/-- The section map obtained by applying `f^♯` and then `f_* d_{X'/Y'}`. -/
def comparisonSection
    {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y')
    {U : (smallEtaleSite X)ᵒᵖ} (t : (commStructureSheaf X).obj.obj U) :
    ((ringedToposHom f).modulePushforward.obj (relativeDifferentials h')).val.obj U :=
  (ToInternal.sectionEquiv (structureSheaf X)
      ((ringedToposHom f).modulePushforward.obj (relativeDifferentials h')) U)
    (((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app
        (relativeDifferentials h')).hom.app U
      ((comparisonSectionTypeHom f h').hom.app U t))

/-- Additivity of the section map underlying the pullback comparison derivation. -/
theorem comparisonSection_add
    {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y')
    {U : (smallEtaleSite X)ᵒᵖ} (a b : (commStructureSheaf X).obj.obj U) :
    comparisonSection f h' (a + b) =
      comparisonSection f h' a + comparisonSection f h' b :=
  sorry

/-- The Leibniz rule for the section map underlying the pullback comparison derivation. -/
theorem comparisonSection_mul
    {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y')
    {U : (smallEtaleSite X)ᵒᵖ} (a b : (commStructureSheaf X).obj.obj U) :
    comparisonSection f h' (a * b) =
      a • comparisonSection f h' b + b • comparisonSection f h' a :=
  sorry

/-- Naturality of the section map underlying the pullback comparison derivation. -/
theorem comparisonSection_naturality
    {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y')
    {U V : (smallEtaleSite X)ᵒᵖ} (ρ : U ⟶ V) (t : (commStructureSheaf X).obj.obj U) :
    comparisonSection f h' ((commStructureSheaf X).obj.map ρ t) =
      (((ringedToposHom f).modulePushforward.obj (relativeDifferentials h')).val.map ρ)
        (comparisonSection f h' t) :=
  sorry

/-- Commutativity of the square makes the pulled differential vanish on the inverse image of
`𝒪_Y`. -/
theorem comparisonSection_base
    {X X' Y Y' : AlgebraicSpace S} (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) {U : (smallEtaleSite X)ᵒᵖ}
    (a : (commInverseImageStructureSheaf h).obj.obj U) :
    comparisonSection f h' ((commInverseImageStructureSheafMap h).hom.app U a) = 0 :=
  sorry

/-- The `Y`-derivation obtained by composing `f^♯` with `f_* d_{X'/Y'}`. -/
def comparisonDerivation
    {X X' Y Y' : AlgebraicSpace S} (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) :
    (toCommPresheaf
      ((ringedToposHom f).modulePushforward.obj (relativeDifferentials h'))).Derivation'
      (commInverseImageStructureSheafMap h).hom where
  d {_} := AddMonoidHom.mk' (comparisonSection f h') (comparisonSection_add f h')
  d_mul := comparisonSection_mul f h'
  d_map := comparisonSection_naturality f h'
  d_app := comparisonSection_base f g h h' sq

/-- Evaluation formula for the derivation underlying the comparison morphism. -/
theorem comparisonDerivation_d
    {X X' Y Y' : AlgebraicSpace S} (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) {U : (smallEtaleSite X)ᵒᵖ}
    (t : (commStructureSheaf X).obj.obj U) :
    (comparisonDerivation f g h h' sq).d t = comparisonSection f h' t :=
  sorry

/-- The adjoint morphism `Ω_{X/Y} ⟶ f_* Ω_{X'/Y'}` induced by the comparison derivation. -/
def comparisonAdjoint
    {X X' Y Y' : AlgebraicSpace S} (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) :
    relativeDifferentials h ⟶
      (ringedToposHom f).modulePushforward.obj (relativeDifferentials h') :=
  (PresheafOfModules.sheafificationHomEquiv.{u} (𝟙 (structureSheaf X).obj)).symm
    ((isUniversal' (commInverseImageStructureSheafMap h).hom).desc
      (comparisonDerivation f g h h' sq))

/-- The canonical pullback comparison `c_f : f^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` attached to a
commutative square of algebraic spaces. -/
def comparison
    {X X' Y Y' : AlgebraicSpace S} (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) :
    (Modules.pullback f).obj (relativeDifferentials h) ⟶ relativeDifferentials h' :=
  ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (comparisonAdjoint f g h h' sq)

/-- A morphism is the differential comparison when its adjoint carries each universal
differential to the differential of the pulled section. -/
def IsComparison
    {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) {Y : AlgebraicSpace S} (h : X ⟶ Y)
    (h' : X' ⟶ Y')
    (tau : (Modules.pullback f).obj (relativeDifferentials h) ⟶ relativeDifferentials h') :
    Prop :=
  ∀ {U : (smallEtaleSite X)ᵒᵖ} (t : (commStructureSheaf X).obj.obj U),
    ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _ tau).val.app U
        ((universalDerivation h).d t) =
      comparisonSection f h' t

/-- The canonical comparison satisfies its sectionwise characterization. -/
theorem comparison_isComparison
    {X X' Y Y' : AlgebraicSpace S} (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) :
    IsComparison f h h' (comparison f g h h' sq) :=
  sorry

/-- The adjoint of the comparison carries the universal differential of `t` to the
differential of its image under `f^♯`. -/
theorem comparison_d
    {X X' Y Y' : AlgebraicSpace S} (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) {U : (smallEtaleSite X)ᵒᵖ}
    (t : (commStructureSheaf X).obj.obj U) :
    ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (comparison f g h h' sq)).val.app U
        ((universalDerivation h).d t) =
      comparisonSection f h' t :=
  sorry

/-- A morphism satisfying the sectionwise characterization equals the canonical comparison. -/
theorem eq_comparison
    {X X' Y Y' : AlgebraicSpace S} (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g)
    {tau : (Modules.pullback f).obj (relativeDifferentials h) ⟶ relativeDifferentials h'}
    (h_tau : IsComparison f h h' tau) :
    tau = comparison f g h h' sq :=
  sorry

/-- A commutative square of algebraic spaces has a unique pullback comparison morphism on
relative differentials. -/
theorem existsUnique_comparison
    {X X' Y Y' : AlgebraicSpace S} (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) :
    ∃! tau : (Modules.pullback f).obj (relativeDifferentials h) ⟶ relativeDifferentials h',
      IsComparison f h h' tau :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Hom.Differentials
