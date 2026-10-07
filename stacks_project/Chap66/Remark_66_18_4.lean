module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap66.Lemma_66_18_3

/-!
# Restriction of étale sheaves along schemes étale over an algebraic space

Lemma 66.18.3 supplies an equivalence between sheaves on the small étale site of an
algebraic space and sheaves on the étale site of algebraic spaces. This remark records
the unique extension of a sheaf along that comparison and the equalizer formula that
computes its sections from a surjective étale scheme presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction of a sheaf on `X_spaces,étale` to the subcategory `X_étale`, given by
continuous direct image along `smallEtaleInclusion X`. -/
abbrev restrictToSmallEtaleSite {S : Scheme.{u}} {X : AlgebraicSpace S} :
    Sheaf (spacesEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
  (smallEtaleInclusion X).sheafPushforwardContinuous
    (Type (u + 1)) (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Sections of a restricted sheaf on `X_étale` are the original sections on the image
object in `X_spaces,étale`. -/
theorem restrictToSmallEtaleSite_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (U' : smallEtaleSite X) :
    (restrictToSmallEtaleSite.obj G).obj.obj (op U') =
      G.obj.obj (op ((smallEtaleInclusion X).obj U')) :=
  rfl

/-- The unique extension of a sheaf on `X_étale` to a sheaf on `X_spaces,étale`, given by
cocontinuous direct image along `smallEtaleInclusion X`. -/
abbrev spacesEtaleExtension {S : Scheme.{u}} {X : AlgebraicSpace S} :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (spacesEtaleTopology X) (Type (u + 1)) :=
  (smallEtaleInclusion X).sheafPushforwardCocontinuous
    (Type (u + 1)) (smallEtaleTopology X) (spacesEtaleTopology X)

/-- `spacesEtaleExtension` is cocontinuous direct image along `smallEtaleInclusion X`. -/
theorem spacesEtaleExtension_eq {S : Scheme.{u}} {X : AlgebraicSpace S} :
    spacesEtaleExtension =
      (smallEtaleInclusion X).sheafPushforwardCocontinuous
        (Type (u + 1)) (smallEtaleTopology X) (spacesEtaleTopology X) :=
  rfl

/-- Every object of `X_spaces,étale` admits a surjective étale morphism from a scheme,
viewed as an object of `X_étale`. -/
theorem exists_surjectiveEtaleSchemeCover {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : spacesEtaleSite X) :
    ∃ (U' : smallEtaleSite X) (π : (smallEtaleInclusion X).obj U' ⟶ U),
      isEtaleFromScheme π.left ∧ Function.Surjective (Points.map π.left) :=
  sorry

/-- A surjective morphism from a scheme étale over `X` is a covering of the corresponding
object in `X_spaces,étale`. -/
theorem ofArrows_schemeCover_mem_spacesEtalePrecoverage {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : spacesEtaleSite X} {U' : smallEtaleSite X}
    (π : (smallEtaleInclusion X).obj U' ⟶ U)
    (hπ : Function.Surjective (Points.map π.left)) :
    Presieve.ofArrows (fun _ : PUnit.{u + 1} ↦ (smallEtaleInclusion X).obj U') (fun _ ↦ π) ∈
      spacesEtalePrecoverage X U :=
  sorry

/-- The kernel pair of an étale morphism from a scheme to an algebraic space étale over `X`
is represented by a scheme étale over `X`. -/
theorem exists_kernelPair_of_isEtaleFromScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : spacesEtaleSite X} {U' : smallEtaleSite X}
    (π : (smallEtaleInclusion X).obj U' ⟶ U) (hp : isEtaleFromScheme π.left) :
    ∃ (R : smallEtaleSite X) (fst snd : R ⟶ U'),
      IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left :=
  sorry

/-- On objects of `X_étale`, the unique extension is identified with the original sheaf by the
right Kan extension counit, so sections may be written as `F` rather than `F'`. -/
def spacesEtaleExtension_obj_smallEtale {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (U' : smallEtaleSite X) :
    (spacesEtaleExtension.obj F).obj.obj (op ((smallEtaleInclusion X).obj U')) ⟶
      F.obj.obj (op U') :=
  ((smallEtaleInclusion X).op.ranCounit.app F.obj).app (op U')

/-- `spacesEtaleExtension_obj_smallEtale` is the right Kan extension counit component. -/
theorem spacesEtaleExtension_obj_smallEtale_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (U' : smallEtaleSite X) :
    spacesEtaleExtension_obj_smallEtale F U' =
      ((smallEtaleInclusion X).op.ranCounit.app F.obj).app (op U') :=
  rfl

/-- The right Kan extension counit is an isomorphism on objects of `X_étale`. -/
instance isIso_spacesEtaleExtension_obj_smallEtale {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (U' : smallEtaleSite X) :
    IsIso (spacesEtaleExtension_obj_smallEtale F U') :=
  sorry

/-- The unique extension of `F` restricts back to `F` on `X_étale`. -/
theorem restrictToSmallEtaleSite_spacesEtaleExtension {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Nonempty (restrictToSmallEtaleSite.obj (spacesEtaleExtension.obj F) ≅ F) :=
  sorry

/-- Remark 66.18.4 (1): let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`F` be a sheaf on the small étale site `X_étale`. A sheaf `G` on `X_spaces,étale` restricts
back to `F` along `smallEtaleInclusion X` if and only if `G` is isomorphic to the unique
extension `spacesEtaleExtension.obj F`. -/
@[stacks 03H7]
theorem unique_spacesEtaleExtension {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1))) :
    Nonempty (restrictToSmallEtaleSite.obj G ≅ F) ↔
      Nonempty (G ≅ spacesEtaleExtension.obj F) :=
  sorry

/-- Remark 66.18.4 (2): let `U → X` be étale as an object of `X_spaces,étale`, and let
`U' → U` be a surjective étale morphism from a scheme. Then `{U' → U}` is a covering in
`X_spaces,étale`. Writing `R` for the kernel pair `U' ×_U U'`, which is a scheme étale
over `X`, the unique extension is computed by the equalizer `F'(U) → F(U') ⇉ F(R)`.
The comparison `F'(U) → F(U')` is restriction along `π` followed by the counit identifying
`F'(U')` with `F(U')`. -/
@[stacks 03H7]
def spacesEtaleExtension_equalizer {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleInclusion X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left) :
    (spacesEtaleExtension.obj F).obj.obj (op U) ⟶ F.obj.obj (op U') :=
  (spacesEtaleExtension.obj F).obj.map π.op ≫ spacesEtaleExtension_obj_smallEtale F U'

/-- `spacesEtaleExtension_equalizer` is restriction along `π` followed by the counit. -/
theorem spacesEtaleExtension_equalizer_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleInclusion X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left) :
    spacesEtaleExtension_equalizer F π fst snd hπ h_pair =
      (spacesEtaleExtension.obj F).obj.map π.op ≫ spacesEtaleExtension_obj_smallEtale F U' :=
  rfl

/-- The comparison `F'(U) → F(U')` equalizes the two maps `F(U') ⇉ F(R)` induced by the
kernel pair. -/
theorem spacesEtaleExtension_equalizer_condition {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleInclusion X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left) :
    spacesEtaleExtension_equalizer F π fst snd hπ h_pair ≫ F.obj.map fst.op =
      spacesEtaleExtension_equalizer F π fst snd hπ h_pair ≫ F.obj.map snd.op :=
  sorry

/-- The comparison `F'(U) → F(U')` as a map into the equalizer of `F.map fst.op` and
`F.map snd.op`. -/
def spacesEtaleExtension_toEqualizer {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleInclusion X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left) :
    (spacesEtaleExtension.obj F).obj.obj (op U) ⟶
      { x : F.obj.obj (op U') // F.obj.map fst.op x = F.obj.map snd.op x } :=
  TypeCat.ofHom fun s ↦
    ⟨spacesEtaleExtension_equalizer F π fst snd hπ h_pair s,
      ConcreteCategory.congr_hom
        (spacesEtaleExtension_equalizer_condition F π fst snd hπ h_pair) s⟩

/-- The underlying map of `spacesEtaleExtension_toEqualizer` is `spacesEtaleExtension_equalizer`. -/
theorem spacesEtaleExtension_toEqualizer_apply {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleInclusion X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left)
    (s : (spacesEtaleExtension.obj F).obj.obj (op U)) :
    (spacesEtaleExtension_toEqualizer F π fst snd hπ h_pair s).val =
      spacesEtaleExtension_equalizer F π fst snd hπ h_pair s :=
  sorry

/-- The induced map from `F'(U)` to the equalizer of `F(U') ⇉ F(R)` is an isomorphism. -/
instance isIso_spacesEtaleExtension_toEqualizer {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U : spacesEtaleSite X} {U' R : smallEtaleSite X}
    (π : (smallEtaleInclusion X).obj U' ⟶ U) (fst snd : R ⟶ U')
    (hπ : Function.Surjective (Points.map π.left))
    (h_pair : IsPullback (ofOverMap fst.left) (ofOverMap snd.left) π.left π.left) :
    IsIso (spacesEtaleExtension_toEqualizer F π fst snd hπ h_pair) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
