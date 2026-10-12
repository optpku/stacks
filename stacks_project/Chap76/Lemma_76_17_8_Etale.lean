/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import stacks_project.Chap70.Lemma_70_7_2_FinitePresentation
public import stacks_project.Chap76.Lemma_76_17_2_Perturbation

/-!
# Étale pullback of perturbation maps of algebraic spaces

An étale square of algebraic spaces identifies relative differentials after pullback.
Transporting an `𝒪_{T₁}`-linear map `θ₁ : a₁^* Ω_{X₁/B₁} ⟶ C_{T₁/T₁'}` along that
identification, the pullback of `θ₁`, and the conormal comparison of the `T`-square
yields `θ₂`, and the Remark 76.17.3 actions then form a commutative square.

`Hom.Differentials.comparison` lives on a duplicate `relativeDifferentials` owner that
cannot be imported with Lemma 76.17.2, so the comparison below is the same canonical
pullback map reconstructed on the 76.7.2/76.17.2 differentials.
-/

@[expose] public section

open CategoryTheory ConcreteCategory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open Sheaf.InternalModule
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}}

/-- The closed square of `Xᵢ ⟶ Bᵢ` induced by a square of first-order thickenings
over a commutative square of primed structure maps. -/
theorem baseCommSq {B1 B2 X1 X1' X2 X2' : AlgebraicSpace S}
    (sB : B2 ⟶ B1) (iX1 : X1 ⟶ X1') (iX2 : X2 ⟶ X2')
    (f : X2 ⟶ X1) (f' : X2' ⟶ X1')
    (sX1 : X1 ⟶ B1) (sX1' : X1' ⟶ B1) (sX2 : X2 ⟶ B2) (sX2' : X2' ⟶ B2)
    (sqX : CommSq f iX2 iX1 f') (sqS : CommSq f' sX2' sX1' sB)
    (hX1 : iX1 ≫ sX1' = sX1) (hX2 : iX2 ≫ sX2' = sX2) :
    CommSq f sX2 sX1 sB := sorry

/-- The underlying type-valued map of the universal derivation `d_{X/Y}`. -/
def universalDerivation_typeHom {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj (structureSheaf X) ⟶
      (ToInternal.underlying (structureSheaf X)).obj (relativeDifferentials h) :=
  InducedCategory.homMk
    { app := fun U ↦ ↾fun t ↦ (universalDerivation h).d (cast rfl t)
      naturality := fun _ _ _ ↦ sorry }

/-- The type-valued composite of `f^♯` with the pushed universal derivation
`f_* d_{X'/Y'}`. -/
def comparisonSectionTypeHom {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y') :
    (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj (structureSheaf X) ⟶
      (ringedToposHom f).toTopos.pushforward.obj
        ((ToInternal.underlying (structureSheaf X')).obj (relativeDifferentials h')) :=
  (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).map (structureSheafMap f) ≫
    (ringPushforwardForgetIso f).hom.app (structureSheaf X') ≫
      (ringedToposHom f).toTopos.pushforward.map (universalDerivation_typeHom h')

/-- The section map obtained by applying `f^♯` and then `f_* d_{X'/Y'}`. -/
def comparisonSection {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y')
    {U : (smallEtaleSite X)ᵒᵖ} (t : (commStructureSheaf X).obj.obj U) :
    ((ringedToposHom f).modulePushforward.obj (relativeDifferentials h')).val.obj U :=
  (ToInternal.sectionEquiv (structureSheaf X)
      ((ringedToposHom f).modulePushforward.obj (relativeDifferentials h')) U)
    (((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app
        (relativeDifferentials h')).hom.app U
      ((comparisonSectionTypeHom f h').hom.app U t))

/-- Additivity of the section map underlying the pullback comparison derivation. -/
theorem comparisonSection_add {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y')
    {U : (smallEtaleSite X)ᵒᵖ} (a b : (commStructureSheaf X).obj.obj U) :
    comparisonSection f h' (a + b) =
      comparisonSection f h' a + comparisonSection f h' b := sorry

/-- The Leibniz rule for the section map underlying the pullback comparison derivation. -/
theorem comparisonSection_mul {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y')
    {U : (smallEtaleSite X)ᵒᵖ} (a b : (commStructureSheaf X).obj.obj U) :
    comparisonSection f h' (a * b) =
      a • comparisonSection f h' b + b • comparisonSection f h' a := sorry

/-- Naturality of the section map underlying the pullback comparison derivation. -/
theorem comparisonSection_naturality {X X' Y' : AlgebraicSpace S} (f : X' ⟶ X) (h' : X' ⟶ Y')
    {U V : (smallEtaleSite X)ᵒᵖ} (ρ : U ⟶ V) (t : (commStructureSheaf X).obj.obj U) :
    comparisonSection f h' ((commStructureSheaf X).obj.map ρ t) =
      (((ringedToposHom f).modulePushforward.obj (relativeDifferentials h')).val.map ρ)
        (comparisonSection f h' t) := sorry

/-- Commutativity of the square makes the pulled differential vanish on the inverse image of
`𝒪_Y`. -/
theorem comparisonSection_base {X X' Y Y' : AlgebraicSpace S}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) {U : (smallEtaleSite X)ᵒᵖ}
    (a : (commInverseImageStructureSheaf h).obj.obj U) :
    comparisonSection f h' ((commInverseImageStructureSheafMap h).hom.app U a) = 0 := sorry

/-- The `Y`-derivation obtained by composing `f^♯` with `f_* d_{X'/Y'}`. -/
def comparisonDerivation {X X' Y Y' : AlgebraicSpace S}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) :
    Hom.derivations h ((Modules.pushforward f).obj (relativeDifferentials h')) where
  d {_} := AddMonoidHom.mk' (comparisonSection f h') (comparisonSection_add f h')
  d_mul := comparisonSection_mul f h'
  d_map := comparisonSection_naturality f h'
  d_app := comparisonSection_base f g h h' sq

/-- The canonical pullback comparison `c_f : f^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` attached to a
commutative square of algebraic spaces, reconstructed on the 76.7.2 differentials. -/
def comparison {X X' Y Y' : AlgebraicSpace S}
    (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
    (sq : f ≫ h = h' ≫ g) :
    (Modules.pullback f).obj (relativeDifferentials h) ⟶ relativeDifferentials h' :=
  ((Modules.pullbackPushforwardAdjunction f).homEquiv
      (relativeDifferentials h) (relativeDifferentials h')).symm
    (SheafOfModules.RingedSite.relativeDifferentialDesc.{u + 1, u, u}
      (commInverseImageStructureSheafMap h)
      (F := (Modules.pushforward f).obj (relativeDifferentials h'))
      (comparisonDerivation f g h h' sq))

/-- For a commutative square of algebraic spaces whose horizontal morphisms are étale,
the canonical pullback comparison on relative differentials is an isomorphism. -/
instance comparison_isIso_of_etale {B1 B2 X1 X2 : AlgebraicSpace S}
    {sB : B2 ⟶ B1} {f : X2 ⟶ X1} {sX1 : X1 ⟶ B1} {sX2 : X2 ⟶ B2}
    (sq : CommSq f sX2 sX1 sB) [Etale f] [Etale sB] :
    IsIso (comparison f sB sX1 sX2 sq.w) := sorry

/-- The canonical identification `a₂^* Ω_{X₂/B₂} ≅ h^* a₁^* Ω_{X₁/B₁}` obtained by
inverting the étale comparison and applying pullback coherence. -/
def pullbackDifferentialsIso {B1 B2 T1 T2 X1 X2 : AlgebraicSpace S}
    (sB : B2 ⟶ B1) (f : X2 ⟶ X1) (h : T2 ⟶ T1)
    (a1 : T1 ⟶ X1) (a2 : T2 ⟶ X2) (sX1 : X1 ⟶ B1) (sX2 : X2 ⟶ B2)
    (sq : CommSq f sX2 sX1 sB) (sqA : CommSq a2 h f a1)
    [Etale f] [Etale sB] :
    (Modules.pullback a2).obj (relativeDifferentials sX2) ≅
      (Modules.pullback h).obj ((Modules.pullback a1).obj (relativeDifferentials sX1)) :=
  (Modules.pullback a2).mapIso
      (@asIso _ _ _ _ (comparison f sB sX1 sX2 sq.w) (comparison_isIso_of_etale sq)).symm ≪≫
    (Modules.pullbackComp a2 f).app (relativeDifferentials sX1) ≪≫
    (Modules.pullbackCongr sqA.w).app (relativeDifferentials sX1) ≪≫
    ((Modules.pullbackComp h a1).app (relativeDifferentials sX1)).symm

/-- The morphism of the canonical pullback-differentials identification is the composite of
the inverse étale comparison and the pullback coherence maps. -/
theorem pullbackDifferentialsIso_hom {B1 B2 T1 T2 X1 X2 : AlgebraicSpace S}
    (sB : B2 ⟶ B1) (f : X2 ⟶ X1) (h : T2 ⟶ T1)
    (a1 : T1 ⟶ X1) (a2 : T2 ⟶ X2) (sX1 : X1 ⟶ B1) (sX2 : X2 ⟶ B2)
    (sq : CommSq f sX2 sX1 sB) (sqA : CommSq a2 h f a1)
    [Etale f] [Etale sB] :
    (pullbackDifferentialsIso sB f h a1 a2 sX1 sX2 sq sqA).hom =
      (Modules.pullback a2).map
          (@asIso _ _ _ _ (comparison f sB sX1 sX2 sq.w) (comparison_isIso_of_etale sq)).inv ≫
        (Modules.pullbackComp a2 f).hom.app (relativeDifferentials sX1) ≫
        (Modules.pullbackCongr sqA.w).hom.app (relativeDifferentials sX1) ≫
        (Modules.pullbackComp h a1).inv.app (relativeDifferentials sX1) := sorry

/-- The pullback of a perturbation map through an étale square of relative differentials and
a square of conormal sheaves. -/
def pullbackPerturbationMap {B1 B2 T1 T1' T2 T2' X1 X2 : AlgebraicSpace S}
    (sB : B2 ⟶ B1) (f : X2 ⟶ X1) (h : T2 ⟶ T1)
    (a1 : T1 ⟶ X1) (a2 : T2 ⟶ X2) (sX1 : X1 ⟶ B1) (sX2 : X2 ⟶ B2)
    (iT1 : T1 ⟶ T1') (iT2 : T2 ⟶ T2') (h' : T2' ⟶ T1')
    (sq : CommSq f sX2 sX1 sB) (sqA : CommSq a2 h f a1)
    (sqT : CommSq h iT2 iT1 h')
    [Etale f] [Etale sB] [IsFirstOrderThickening iT1] [IsFirstOrderThickening iT2]
    (θ1 : (Modules.pullback a1).obj (relativeDifferentials sX1) ⟶ Hom.conormalSheaf iT1) :
    (Modules.pullback a2).obj (relativeDifferentials sX2) ⟶ Hom.conormalSheaf iT2 :=
  (pullbackDifferentialsIso sB f h a1 a2 sX1 sX2 sq sqA).hom ≫
    (Modules.pullback h).map θ1 ≫ Hom.Conormal.map sqT

/-- The pullback perturbation map is the differential identification followed by the pulled
map and the conormal comparison. -/
theorem pullbackPerturbationMap_def {B1 B2 T1 T1' T2 T2' X1 X2 : AlgebraicSpace S}
    (sB : B2 ⟶ B1) (f : X2 ⟶ X1) (h : T2 ⟶ T1)
    (a1 : T1 ⟶ X1) (a2 : T2 ⟶ X2) (sX1 : X1 ⟶ B1) (sX2 : X2 ⟶ B2)
    (iT1 : T1 ⟶ T1') (iT2 : T2 ⟶ T2') (h' : T2' ⟶ T1')
    (sq : CommSq f sX2 sX1 sB) (sqA : CommSq a2 h f a1)
    (sqT : CommSq h iT2 iT1 h')
    [Etale f] [Etale sB] [IsFirstOrderThickening iT1] [IsFirstOrderThickening iT2]
    (θ1 : (Modules.pullback a1).obj (relativeDifferentials sX1) ⟶ Hom.conormalSheaf iT1) :
    pullbackPerturbationMap sB f h a1 a2 sX1 sX2 iT1 iT2 h' sq sqA sqT θ1 =
      (pullbackDifferentialsIso sB f h a1 a2 sX1 sX2 sq sqA).hom ≫
        (Modules.pullback h).map θ1 ≫ Hom.Conormal.map sqT := sorry

/-- Perturbations transported through an étale square preserve the commutative square of
ambient morphisms. -/
theorem perturbation_commSq_of_etale
    {B1 B2 T1 T1' T2 T2' X1 X1' X2 X2' : AlgebraicSpace S}
    (sB : B2 ⟶ B1)
    (sX1 : X1 ⟶ B1) (sX1' : X1' ⟶ B1) (sT1' : T1' ⟶ B1)
    (sX2 : X2 ⟶ B2) (sX2' : X2' ⟶ B2) (sT2' : T2' ⟶ B2)
    (iT1 : T1 ⟶ T1') (iX1 : X1 ⟶ X1') (iT2 : T2 ⟶ T2') (iX2 : X2 ⟶ X2')
    (a1 : T1 ⟶ X1) (a1' : T1' ⟶ X1') (a2 : T2 ⟶ X2) (a2' : T2' ⟶ X2')
    (h : T2 ⟶ T1) (h' : T2' ⟶ T1') (f : X2 ⟶ X1) (f' : X2' ⟶ X1')
    [IsFirstOrderThickening iT1] [IsFirstOrderThickening iX1]
    [IsFirstOrderThickening iT2] [IsFirstOrderThickening iX2]
    [Etale f] [Etale sB]
    (sqA1 : CommSq a1 iT1 iX1 a1') (sqA2 : CommSq a2 iT2 iX2 a2')
    (sqT : CommSq h iT2 iT1 h') (sqX : CommSq f iX2 iX1 f')
    (sq0 : CommSq a2 h f a1) (sq1 : CommSq a2' h' f' a1')
    (sqS : CommSq f' sX2' sX1' sB)
    (hX1 : iX1 ≫ sX1' = sX1) (hX2 : iX2 ≫ sX2' = sX2)
    (θ1 : (Modules.pullback a1).obj (relativeDifferentials sX1) ⟶ Hom.conormalSheaf iT1)
    (b1' : T1' ⟶ X1') (b2' : T2' ⟶ X2')
    (hb1 : IsPerturbation sX1 sT1' sX1' iT1 iX1 a1 a1' sqA1 θ1 b1')
    (hb2 : IsPerturbation sX2 sT2' sX2' iT2 iX2 a2 a2' sqA2
      (pullbackPerturbationMap sB f h a1 a2 sX1 sX2 iT1 iT2 h'
        (baseCommSq sB iX1 iX2 f f' sX1 sX1' sX2 sX2' sqX sqS hX1 hX2) sq0 sqT θ1)
      b2') :
    CommSq b2' h' f' b1' := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
