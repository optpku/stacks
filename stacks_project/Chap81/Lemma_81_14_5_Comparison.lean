module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap71.Lemma_71_6_12_Pullback
public import stacks_project.Chap81.Lemma_81_14_5_Lift

/-!
# Scheme-theoretic images and strict transforms of algebraic spaces

This file embeds the Chap71 strict transform of a quasi-compact scheme-theoretic
image into a blown-up fibre product, and compares it with the image of the
lifted morphism. The strict transform of `Z ⊂ X ×_B Y` is the closed subspace of
`Z ×_X X'` cut out by sections supported on the exceptional divisor, included
into `X' ×_B Y`.

Chap71 `strictTransform` and Chap67 scheme-theoretic image currently rebuild the
broken `Lemma_66_4_2_Comparison`. The strict transform is reconstructed as the
quasi-compact scheme-theoretic image of the open complement of
`pr_{B'}^{-1} E` in `X ×_B B'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- For a quasi-compact morphism of algebraic spaces, the kernel of
`𝒪_Y ⟶ f_* 𝒪_X` is a quasi-coherent ideal sheaf on `Y`. -/
instance instIsQuasiCoherent_idealSheafSubobject_of_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] :
    IsQuasiCoherent (idealSheafSubobject f) :=
  sorry

end Hom

/-- The first projection of the canonical quasi-compact scheme-theoretic image of
`q : V ⟶ X ×_B Y`. -/
noncomputable def imageFst {S : Scheme.{u}} {B X Y V : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q] :
    subscheme (Hom.idealSheafSubobject q) ⟶ X :=
  subschemeι (Hom.idealSheafSubobject q) ≫ pullback.fst f g

/-- `imageFst` is the composite of the kernel-subscheme inclusion with the first
projection of `X ×_B Y`. -/
theorem imageFst_eq {S : Scheme.{u}} {B X Y V : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q] :
    imageFst f g q = subschemeι (Hom.idealSheafSubobject q) ≫ pullback.fst f g :=
  sorry

/-- The morphism of algebraic spaces associated to a Yoneda section of `X`. -/
def homOfYonedaSection {S : Scheme.{u}} {X : AlgebraicSpace S} {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) : ofOver U.unop ⟶ X :=
  yonedaEquiv.symm α

/-- `homOfYonedaSection` is the Yoneda transpose of a section of the functor of points. -/
theorem homOfYonedaSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) :
    homOfYonedaSection α = yonedaEquiv.symm α :=
  sorry

/-- A section of the functor of points of `X` misses the closed image of `i` when the
induced map on points lands in the complement of `|Z|`. -/
def missesClosedImage {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U) : Prop :=
  Set.range (Points.map (homOfYonedaSection α)) ⊆ (Set.range (Points.map i))ᶜ

/-- Missing the closed image of `i` is the point-set condition on the Yoneda morphism
associated to a section. -/
theorem missesClosedImage_iff {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U) :
    missesClosedImage i α ↔
      Set.range (Points.map (homOfYonedaSection α)) ⊆ (Set.range (Points.map i))ᶜ :=
  sorry

/-- The subfunctor of maps into `X` whose image of points misses `|Z|`. -/
def closedImmersionComplementSubfunctor {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] : Subfunctor X.functorOfPoints where
  obj U := {α | missesClosedImage i α}
  map := sorry

/-- Membership in the complement subfunctor is the missing-closed-image condition. -/
theorem mem_closedImmersionComplementSubfunctor_obj {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] {U : (Over S)ᵒᵖ} (α : X.functorOfPoints.obj U) :
    α ∈ (closedImmersionComplementSubfunctor i).obj U ↔ missesClosedImage i α :=
  sorry

/-- The open complement algebraic space `X \ Z` of a closed immersion `i : Z ⟶ X`. -/
def closedImmersionComplement {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    AlgebraicSpace S :=
  ofFunctor (closedImmersionComplementSubfunctor i).toFunctor sorry sorry sorry

/-- The open immersion of the complement `X \ Z` into `X`. -/
def closedImmersionComplementι {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionComplement i ⟶ X :=
  (closedImmersionComplementSubfunctor i).ι

/-- The inclusion of the complement of a closed immersion is an open immersion. -/
instance instIsOpenImmersion_closedImmersionComplementι {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] : IsOpenImmersion (closedImmersionComplementι i) :=
  sorry

/-- The complement of a closed immersion, as an open subspace of `X`. -/
def closedImmersionComplementSubspace {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] : OpenSubspace X :=
  OpenSubspace.ofι (closedImmersionComplementι i)

/-- The complement space is included by an open immersion whose functor of points is
the missing-`|Z|` subfunctor. -/
theorem closedImmersionComplement_spec {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (closedImmersionComplement i).functorOfPoints =
        (closedImmersionComplementSubfunctor i).toFunctor ∧
      closedImmersionComplementι i = (closedImmersionComplementSubfunctor i).ι ∧
      IsOpenImmersion (closedImmersionComplementι i) :=
  sorry

/-- The fibre-product ambient algebraic space `X ×_B B'` of a strict-transform
construction. -/
abbrev strictTransformAmbient {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B) (f : X ⟶ B) :
    AlgebraicSpace S :=
  pullback f b

/-- The ambient algebraic space is the fibre product of `f` and `b`. -/
theorem strictTransformAmbient_eq {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B) (f : X ⟶ B) :
    strictTransformAmbient b f = pullback f b :=
  sorry

/-- The closed subspace `pr_{B'}^{-1} E ⊂ X ×_B B'` obtained by pulling `E` back
along the second projection. -/
def strictTransformSupport {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B)
    (E : ClosedSubspace B') (f : X ⟶ B) :
    ClosedSubspace (strictTransformAmbient b f) :=
  ClosedSubspace.inverseImage E (pullback.snd f b)

/-- The pulled-back support is the inverse image of `E` along `pr_{B'}`. -/
theorem strictTransformSupport_eq {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B)
    (E : ClosedSubspace B') (f : X ⟶ B) :
    strictTransformSupport b E f = ClosedSubspace.inverseImage E (pullback.snd f b) :=
  sorry

/-- The open subspace of `X ×_B B'` complementary to `|pr_{B'}^{-1} E|`. -/
def strictTransformOpenComplement {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B)
    (E : ClosedSubspace B') (f : X ⟶ B) :
    OpenSubspace (strictTransformAmbient b f) :=
  closedImmersionComplementSubspace (strictTransformSupport b E f).ι

/-- The complementary open subspace is the open complement of the pulled-back support. -/
theorem strictTransformOpenComplement_eq {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B)
    (E : ClosedSubspace B') (f : X ⟶ B) :
    strictTransformOpenComplement b E f =
      closedImmersionComplementSubspace (strictTransformSupport b E f).ι :=
  sorry

/-- The strict transform of `X` is the scheme-theoretic image of the complementary
open of `|pr_{B'}^{-1} E|` in `X ×_B B'`. -/
noncomputable def strictTransform {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B)
    (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    ClosedSubspace (strictTransformAmbient b f) :=
  ClosedSubspace.ofQuasiCoherentIdeal
    (Hom.idealSheafSubobject (strictTransformOpenComplement b E f).ι)

/-- The inclusion of the strict transform is the closed immersion cut out by the
kernel of the complementary open. -/
theorem strictTransform_ι {S : Scheme.{u}} {B B' X : AlgebraicSpace S} (b : B' ⟶ B)
    (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    (strictTransform b E f).ι =
      subschemeι (Hom.idealSheafSubobject (strictTransformOpenComplement b E f).ι) :=
  sorry

/-- The canonical projection from the strict transform of `X` along `b` to `X`. -/
noncomputable def strictTransformFst {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    (strictTransform b E f).X ⟶ X :=
  (strictTransform b E f).ι ≫ pullback.fst f b

/-- `strictTransformFst` is the composite of the strict-transform inclusion with
the first projection of `X ×_B B'`. -/
theorem strictTransformFst_eq {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransformFst b E f = (strictTransform b E f).ι ≫ pullback.fst f b :=
  sorry

/-- The canonical projection from the strict transform of `X` along `b` to `B'`. -/
noncomputable def strictTransformSnd {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    (strictTransform b E f).X ⟶ B' :=
  (strictTransform b E f).ι ≫ pullback.snd f b

/-- `strictTransformSnd` is the composite of the strict-transform inclusion with
the second projection of `X ×_B B'`. -/
theorem strictTransformSnd_eq {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransformSnd b E f = (strictTransform b E f).ι ≫ pullback.snd f b :=
  sorry

/-- The two canonical projections from a strict transform form a commutative
square. -/
theorem strictTransform_condition {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransformFst b E f ≫ f = strictTransformSnd b E f ≫ b :=
  sorry

/-- The complementary open of the exceptional divisor in `Z ×_X X'` is
quasi-compact, because that divisor is effective Cartier. -/
instance instQuasiCompact_strictTransformOpenComplement_imageFst
    {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) [IsBlowup b center] :
    QuasiCompact
      (strictTransformOpenComplement b (ClosedSubspace.inverseImage center b) (imageFst f g q)).ι :=
  sorry

/-- The two legs defining the closed immersion of the strict transform of the
image of `q` into `X' ×_B Y` commute over `B`. -/
theorem strictTransformImageMap_condition {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) [IsBlowup b center] :
    strictTransformSnd b (ClosedSubspace.inverseImage center b) (imageFst f g q) ≫ (b ≫ f) =
      (strictTransformFst b (ClosedSubspace.inverseImage center b) (imageFst f g q) ≫
        subschemeι (Hom.idealSheafSubobject q) ≫ pullback.snd f g) ≫ g :=
  sorry

/-- The canonical closed immersion of the strict transform of the scheme-theoretic
image of `q` into `X' ×_B Y`. -/
noncomputable def strictTransformImageMap {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) [IsBlowup b center] :
    (strictTransform b (ClosedSubspace.inverseImage center b) (imageFst f g q)).X ⟶
      pullback (b ≫ f) g :=
  pullback.lift
    (strictTransformSnd b (ClosedSubspace.inverseImage center b) (imageFst f g q))
    (strictTransformFst b (ClosedSubspace.inverseImage center b) (imageFst f g q) ≫
      subschemeι (Hom.idealSheafSubobject q) ≫ pullback.snd f g)
    (strictTransformImageMap_condition f g q b center)

/-- The first projection of `strictTransformImageMap` is the projection of the
strict transform to `X'`. -/
theorem strictTransformImageMap_fst {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) [IsBlowup b center] :
    strictTransformImageMap f g q b center ≫ pullback.fst (b ≫ f) g =
      strictTransformSnd b (ClosedSubspace.inverseImage center b) (imageFst f g q) :=
  sorry

/-- The second projection of `strictTransformImageMap` is induced by the
projection of the image of `q` to `Y`. -/
theorem strictTransformImageMap_snd {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) [IsBlowup b center] :
    strictTransformImageMap f g q b center ≫ pullback.snd (b ≫ f) g =
      strictTransformFst b (ClosedSubspace.inverseImage center b) (imageFst f g q) ≫
        subschemeι (Hom.idealSheafSubobject q) ≫ pullback.snd f g :=
  sorry

/-- The strict-transform map into the blown-up fibre product is a closed
immersion. -/
instance instIsClosedImmersion_strictTransformImageMap {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (b : X' ⟶ X) (center : ClosedSubspace X) [IsBlowup b center] :
    IsClosedImmersion (strictTransformImageMap f g q b center) :=
  sorry


/-- The closed immersion of the scheme-theoretic image of the admissible lift
`V ⟶ X' ×_B Y`. -/
noncomputable def liftAdmissibleImageι {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    subscheme (Hom.idealSheafSubobject (liftAdmissiblePullback f g q U b qU hiso hqU)) ⟶
      pullback (b ≫ f) g :=
  subschemeι (Hom.idealSheafSubobject (liftAdmissiblePullback f g q U b qU hiso hqU))

/-- `liftAdmissibleImageι` is the closed immersion cut out by the kernel of the
admissible lift. -/
theorem liftAdmissibleImageι_eq {S : Scheme.{u}} {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    liftAdmissibleImageι f g q U b qU hiso hqU =
      subschemeι (Hom.idealSheafSubobject
        (liftAdmissiblePullback f g q U b qU hiso hqU)) :=
  sorry

/-- The scheme-theoretic image of the admissible lift is a closed immersion. -/
instance instIsClosedImmersion_liftAdmissibleImageι {S : Scheme.{u}}
    {B X Y V X' : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (q : V ⟶ pullback f g) [QuasiCompact q]
    (U : OpenSubspace X) (b : X' ⟶ X)
    (qU : V ⟶ U.X) (hiso : IsIso (pullback.fst U.ι b))
    (hqU : qU ≫ U.ι = q ≫ pullback.fst f g) :
    IsClosedImmersion (liftAdmissibleImageι f g q U b qU hiso hqU) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
