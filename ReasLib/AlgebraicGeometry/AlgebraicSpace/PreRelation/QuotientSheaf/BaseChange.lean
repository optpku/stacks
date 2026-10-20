module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.Invariant

/-!
# Base change of invariant quotient sheaves

The quotient sheaf of an invariant base change is canonically identified with the pullback of
the original quotient sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits ConcreteCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The second projection is invariant for the base-changed pre-relation. -/
theorem isInvariantHom_pullback_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.baseChange hφ f).IsInvariantHom (pullback.snd φ f) :=
  sorry

/-- The two maps `U' ⟶ X'` and `U' ⟶ U/R` agree over `X`. -/
private theorem toQuotientSheafPullback_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    toSheaf.map (pullback.snd φ f).left ≫ toSheaf.map f.left =
      toSheaf.map (pullback.fst φ f).left ≫ P.quotientMap ≫ P.quotientSheafFactor hφ :=
  sorry

/-- The canonical morphism `U' ⟶ X' ×_X U/R` of fppf sheaves. -/
def toQuotientSheafPullback {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    toSheaf.obj (pullback φ f).left ⟶
      pullback (toSheaf.map f.left) (P.quotientSheafFactor hφ) :=
  pullback.lift
    (toSheaf.map (pullback.snd φ f).left)
    (toSheaf.map (pullback.fst φ f).left ≫ P.quotientMap)
    (P.toQuotientSheafPullback_condition hφ f)

/-- The first projection of `toQuotientSheafPullback` is the universe-raised second
pullback projection. -/
theorem toQuotientSheafPullback_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    P.toQuotientSheafPullback hφ f ≫
        pullback.fst (toSheaf.map f.left) (P.quotientSheafFactor hφ) =
      toSheaf.map (pullback.snd φ f).left :=
  sorry

/-- The second projection of `toQuotientSheafPullback` is `U' ⟶ U ⟶ U/R`. -/
theorem toQuotientSheafPullback_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    P.toQuotientSheafPullback hφ f ≫
        pullback.snd (toSheaf.map f.left) (P.quotientSheafFactor hφ) =
      toSheaf.map (pullback.fst φ f).left ≫ P.quotientMap :=
  sorry

/-- The morphism `U' ⟶ X' ×_X U/R` equalizes the base-changed parallel pair. -/
theorem toQuotientSheafPullback_equalizes {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    toSheaf.map (P.baseChange hφ f).t.left ≫ P.toQuotientSheafPullback hφ f =
      toSheaf.map (P.baseChange hφ f).s.left ≫ P.toQuotientSheafPullback hφ f :=
  sorry

/-- Related `T`-points of `U'` remain related after applying `U' ⟶ U`. -/
theorem schemePointRel_map_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) {T : Over S}
    {x y : (pullback φ f).left.functorOfPoints.obj (op T)}
    (h : (P.baseChange hφ f).schemePointRel T x y) :
    P.schemePointRel T ((pullback.fst φ f).left.app (op T) x)
      ((pullback.fst φ f).left.app (op T) y) :=
  sorry

/-- Naturality of the quotient-presheaf map induced by `U' ⟶ U`. -/
theorem quotientPresheafPullbackFst_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    ((P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).map g ≫
        TypeCat.ofHom (fun x ↦
          ULift.up <|
            Quot.map ((pullback.fst φ f).left.app T')
              (fun _ _ h ↦ P.schemePointRel_map_fst hφ f h) x.down) =
      TypeCat.ofHom (fun x ↦
        ULift.up <|
          Quot.map ((pullback.fst φ f).left.app T)
            (fun _ _ h ↦ P.schemePointRel_map_fst hφ f h) x.down) ≫
        (P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).map g :=
  sorry

/-- The map of universe-raised quotient presheaves induced by `U' ⟶ U`. -/
def quotientPresheafPullbackFst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u} ⟶
      P.quotientPresheaf ⋙ uliftFunctor.{u + 1, u} where
  app T :=
    TypeCat.ofHom fun x ↦
      ULift.up <|
        Quot.map ((pullback.fst φ f).left.app T)
          (fun _ _ h ↦ P.schemePointRel_map_fst hφ f h) x.down
  naturality := fun {T T'} g => P.quotientPresheafPullbackFst_naturality hφ f g

/-- The component of `quotientPresheafPullbackFst` is `Quot.map` of `U' ⟶ U`. -/
theorem quotientPresheafPullbackFst_app {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) (T : (Over S)ᵒᵖ)
    (x : ((P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).obj T) :
    (P.quotientPresheafPullbackFst hφ f).app T x =
      ULift.up
        (Quot.map ((pullback.fst φ f).left.app T)
          (fun _ _ h ↦ P.schemePointRel_map_fst hφ f h) x.down) :=
  sorry

/-- The two maps out of the universe-raised quotient of `U'` agree over `X`. -/
private theorem quotientPresheafBaseChangeHom_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.baseChange hφ f).quotientPresheafFactor (P.isInvariantHom_pullback_snd hφ f) ≫
        (toSheaf.map f.left).hom =
      P.quotientPresheafPullbackFst hφ f ≫ P.quotientPresheafFactor hφ :=
  sorry

/-- The forward comparison of universe-raised quotient presheaves with the presheaf fibre
product `X' ×_X (U/~)`. -/
def quotientPresheafBaseChangeHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u} ⟶
      pullback (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ) :=
  pullback.lift
    ((P.baseChange hφ f).quotientPresheafFactor (P.isInvariantHom_pullback_snd hφ f))
    (P.quotientPresheafPullbackFst hφ f)
    (P.quotientPresheafBaseChangeHom_condition hφ f)

/-- A representative of a class in `U(T)/R` compatible with a point of `X'(T)` maps to the
same point of `X`. -/
private theorem quotientPresheafFactor_out {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) (T : (Over S)ᵒᵖ)
    (p : pullback ((toSheaf.map f.left).hom.app T) ((P.quotientPresheafFactor hφ).app T)) :
    φ.left.app T
        (Quot.out
          (ConcreteCategory.hom (pullback.snd ((toSheaf.map f.left).hom.app T)
              ((P.quotientPresheafFactor hφ).app T)) p).down) =
      f.left.app T
        (ConcreteCategory.hom (pullback.fst ((toSheaf.map f.left).hom.app T)
            ((P.quotientPresheafFactor hφ).app T)) p).down :=
  sorry

/-- The pointwise inverse of the universe-raised quotient comparison, sending a compatible
pair `(x', [u])` to the class of the induced `T`-point of `U'`. -/
def quotientPresheafBaseChangeInvApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) (T : (Over S)ᵒᵖ) :
    pullback ((toSheaf.map f.left).hom.app T) ((P.quotientPresheafFactor hφ).app T) ⟶
      ((P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).obj T :=
  TypeCat.ofHom fun p ↦
    ULift.up <|
      Quot.mk ((P.baseChange hφ f).schemePointRel T.unop) <|
        pullbackSchemePoint f
          (ConcreteCategory.hom (pullback.fst ((toSheaf.map f.left).hom.app T)
              ((P.quotientPresheafFactor hφ).app T)) p).down
          (Quot.out
            (ConcreteCategory.hom (pullback.snd ((toSheaf.map f.left).hom.app T)
                ((P.quotientPresheafFactor hφ).app T)) p).down)
          (P.quotientPresheafFactor_out hφ f T p)

/-- The pointwise inverse quotient comparison is natural in the test scheme. -/
theorem quotientPresheafBaseChangeInv_naturality {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    (pullback (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ)).map g ≫
        ((PreservesPullback.iso
          ((evaluation ((Over S)ᵒᵖ) (Type (u + 1))).obj T')
          (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ)).hom ≫
          P.quotientPresheafBaseChangeInvApp hφ f T') =
      ((PreservesPullback.iso
          ((evaluation ((Over S)ᵒᵖ) (Type (u + 1))).obj T)
          (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ)).hom ≫
        P.quotientPresheafBaseChangeInvApp hφ f T) ≫
          ((P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).map g :=
  sorry

/-- The inverse comparison of the universe-raised quotient presheaf with the presheaf
fibre product, evaluated after identifying objectwise pullbacks. -/
def quotientPresheafBaseChangeInv {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    pullback (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ) ⟶
      (P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u} where
  app T :=
    (PreservesPullback.iso
          ((evaluation ((Over S)ᵒᵖ) (Type (u + 1))).obj T)
          (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ)).hom ≫
      P.quotientPresheafBaseChangeInvApp hφ f T
  naturality := fun {T T'} g => P.quotientPresheafBaseChangeInv_naturality hφ f g

/-- The component of `quotientPresheafBaseChangeInv` is the evaluation comparison followed
by the pointwise inverse. -/
theorem quotientPresheafBaseChangeInv_app {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) (T : (Over S)ᵒᵖ) :
    (P.quotientPresheafBaseChangeInv hφ f).app T =
      (PreservesPullback.iso
            ((evaluation ((Over S)ᵒᵖ) (Type (u + 1))).obj T)
            (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ)).hom ≫
        P.quotientPresheafBaseChangeInvApp hφ f T :=
  sorry

/-- The forward and reverse quotient comparisons are mutually inverse on sections. -/
theorem quotientPresheafBaseChangeIsoApp_inverse_laws {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X}
    (hφ : P.IsInvariantHom φ) (f : X' ⟶ X) (T : (Over S)ᵒᵖ) :
    ((P.quotientPresheafBaseChangeHom hφ f).app T ≫
        (P.quotientPresheafBaseChangeInv hφ f).app T = 𝟙 _) ∧
      ((P.quotientPresheafBaseChangeInv hφ f).app T ≫
        (P.quotientPresheafBaseChangeHom hφ f).app T = 𝟙 _) :=
  sorry

/-- The objectwise identification of the universe-raised quotient of `U'` with the fibre
product of `X'` and `U/~` over `X`. -/
def quotientPresheafBaseChangeIsoApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) (T : (Over S)ᵒᵖ) :
    ((P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).obj T ≅
      (pullback (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ)).obj T :=
  Iso.mk ((P.quotientPresheafBaseChangeHom hφ f).app T)
    ((P.quotientPresheafBaseChangeInv hφ f).app T)
    (P.quotientPresheafBaseChangeIsoApp_inverse_laws hφ f T).1
    (P.quotientPresheafBaseChangeIsoApp_inverse_laws hφ f T).2

/-- The hom-component of `quotientPresheafBaseChangeIsoApp` is the forward comparison. -/
theorem quotientPresheafBaseChangeIsoApp_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) (T : (Over S)ᵒᵖ) :
    (P.quotientPresheafBaseChangeIsoApp hφ f T).hom =
      (P.quotientPresheafBaseChangeHom hφ f).app T :=
  sorry

/-- Naturality of the objectwise quotient comparison in `T`. -/
theorem quotientPresheafBaseChangeIso_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) {T T' : (Over S)ᵒᵖ} (g : T ⟶ T') :
    ((P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u}).map g ≫
        (P.quotientPresheafBaseChangeIsoApp hφ f T').hom =
      (P.quotientPresheafBaseChangeIsoApp hφ f T).hom ≫
        (pullback (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ)).map g :=
  sorry

/-- The canonical isomorphism of universe-raised quotient presheaves
`(U'/~) ≅ X' ×_X (U/~)`. -/
def quotientPresheafBaseChangeIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.baseChange hφ f).quotientPresheaf ⋙ uliftFunctor.{u + 1, u} ≅
      pullback (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ) :=
  NatIso.ofComponents (P.quotientPresheafBaseChangeIsoApp hφ f)
    (P.quotientPresheafBaseChangeIso_naturality hφ f)

/-- The forward sheaf morphism `U'/R' ⟶ X' ×_X U/R` obtained by descending
`toQuotientSheafPullback` along the coequalizer `U' ⟶ U'/R'`. -/
def quotientSheafBaseChangeHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.baseChange hφ f).quotientSheaf ⟶
      pullback (toSheaf.map f.left) (P.quotientSheafFactor hφ) :=
  (P.baseChange hφ f).quotientSheafLift (P.toQuotientSheafPullback hφ f)
    (P.toQuotientSheafPullback_equalizes hφ f)

/-- The first cospan comparison identifying `X' ⟶ X` with its sheafification. -/
private theorem quotientSheafCospanMap_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    toSheaf.map f.left ≫ (sheafificationIso (toSheaf.obj X.left)).hom =
      (sheafificationIso (toSheaf.obj X'.left)).hom ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (toSheaf.map f.left).hom :=
  sorry

/-- The second cospan comparison identifying `U/R ⟶ X` with sheafification of the
presheaf factor. -/
private theorem quotientSheafCospanMap_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    P.quotientSheafFactor hφ ≫ (sheafificationIso (toSheaf.obj X.left)).hom =
      𝟙 _ ≫
        (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (P.quotientPresheafFactor hφ) :=
  sorry

/-- The comparison of fibre products of sheaves along sheafification of the cospan
`X' ⟶ X ← U/R`. -/
private def quotientSheafCospanMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    pullback (toSheaf.map f.left) (P.quotientSheafFactor hφ) ⟶
      pullback
        ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (toSheaf.map f.left).hom)
        ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (P.quotientPresheafFactor hφ)) :=
  pullback.map _ _ _ _
    (sheafificationIso (toSheaf.obj X'.left)).hom (𝟙 _)
    (sheafificationIso (toSheaf.obj X.left)).hom
    (P.quotientSheafCospanMap_fst hφ f) (P.quotientSheafCospanMap_snd hφ f)

/-- The reverse cospan comparison, using the inverses of the sheafification isos. -/
private theorem quotientSheafCospanMap_inv_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (toSheaf.map f.left).hom) ≫
        (sheafificationIso (toSheaf.obj X.left)).inv =
      (sheafificationIso (toSheaf.obj X'.left)).inv ≫ toSheaf.map f.left :=
  sorry

/-- The reverse cospan comparison on the `U/R` leg. -/
private theorem quotientSheafCospanMap_inv_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (P.quotientPresheafFactor hφ)) ≫
        (sheafificationIso (toSheaf.obj X.left)).inv =
      𝟙 _ ≫ P.quotientSheafFactor hφ :=
  sorry

/-- The inverse comparison of fibre products of sheaves along sheafification of the
cospan `X' ⟶ X ← U/R`. -/
private def quotientSheafCospanMapInv {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    pullback
        ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (toSheaf.map f.left).hom)
        ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (P.quotientPresheafFactor hφ)) ⟶
      pullback (toSheaf.map f.left) (P.quotientSheafFactor hφ) :=
  pullback.map _ _ _ _
    (sheafificationIso (toSheaf.obj X'.left)).inv (𝟙 _)
    (sheafificationIso (toSheaf.obj X.left)).inv
    (P.quotientSheafCospanMap_inv_fst hφ f) (P.quotientSheafCospanMap_inv_snd hφ f)

/-- The pullback transports along sheafification are mutually inverse. -/
private theorem quotientSheafCospanIso_inverse_laws {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.quotientSheafCospanMap hφ f ≫ P.quotientSheafCospanMapInv hφ f = 𝟙 _) ∧
      (P.quotientSheafCospanMapInv hφ f ≫ P.quotientSheafCospanMap hφ f = 𝟙 _) :=
  sorry

/-- Sheafification identifies the cospan `X' ⟶ X ← U/R` with the image of the
presheaf-level cospan. -/
private def quotientSheafCospanIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    pullback (toSheaf.map f.left) (P.quotientSheafFactor hφ) ≅
      pullback
        ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (toSheaf.map f.left).hom)
        ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
          (P.quotientPresheafFactor hφ)) :=
  Iso.mk (P.quotientSheafCospanMap hφ f) (P.quotientSheafCospanMapInv hφ f)
    (P.quotientSheafCospanIso_inverse_laws hφ f).1
    (P.quotientSheafCospanIso_inverse_laws hφ f).2

/-- The inverse sheaf morphism `X' ×_X U/R ⟶ U'/R'`, obtained by sheafifying the
presheaf comparison and transporting along preservation of pullbacks. -/
def quotientSheafBaseChangeInv {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    pullback (toSheaf.map f.left) (P.quotientSheafFactor hφ) ⟶
      (P.baseChange hφ f).quotientSheaf :=
  (P.quotientSheafCospanIso hφ f).hom ≫
    (PreservesPullback.iso
          (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
          (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ)).inv ≫
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
        (P.quotientPresheafBaseChangeIso hφ f).inv

/-- The forward and reverse sheaf quotient comparisons are mutually inverse. -/
theorem quotientSheafBaseChangeIso_inverse_laws {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.quotientSheafBaseChangeHom hφ f ≫ P.quotientSheafBaseChangeInv hφ f = 𝟙 _) ∧
      (P.quotientSheafBaseChangeInv hφ f ≫ P.quotientSheafBaseChangeHom hφ f = 𝟙 _) :=
  sorry

/-- The canonical isomorphism of fppf sheaves `U'/R' ≅ X' ×_X U/R`. -/
def quotientSheafBaseChangeIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.baseChange hφ f).quotientSheaf ≅
      pullback (toSheaf.map f.left) (P.quotientSheafFactor hφ) :=
  Iso.mk (P.quotientSheafBaseChangeHom hφ f) (P.quotientSheafBaseChangeInv hφ f)
    (P.quotientSheafBaseChangeIso_inverse_laws hφ f).1
    (P.quotientSheafBaseChangeIso_inverse_laws hφ f).2

/-- The forward map of `quotientSheafBaseChangeIso` is `quotientSheafBaseChangeHom`. -/
theorem quotientSheafBaseChangeIso_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.quotientSheafBaseChangeIso hφ f).hom = P.quotientSheafBaseChangeHom hφ f :=
  sorry

/-- The inverse map of `quotientSheafBaseChangeIso` is `quotientSheafBaseChangeInv`. -/
theorem quotientSheafBaseChangeIso_inv {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.quotientSheafBaseChangeIso hφ f).inv = P.quotientSheafBaseChangeInv hφ f :=
  sorry

/-- The first projection of the comparison iso is the structure map of `U'/R'` over `X'`. -/
theorem quotientSheafBaseChangeIso_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.quotientSheafBaseChangeIso hφ f).hom ≫
        pullback.fst (toSheaf.map f.left) (P.quotientSheafFactor hφ) =
      (P.baseChange hφ f).quotientSheafFactor (P.isInvariantHom_pullback_snd hφ f) :=
  sorry

/-- The composite `U' ⟶ U ⟶ U/R` equalizes the base-changed parallel pair. -/
theorem quotientMap_fst_equalizes {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    toSheaf.map (P.baseChange hφ f).t.left ≫
        (toSheaf.map (pullback.fst φ f).left ≫ P.quotientMap) =
      toSheaf.map (P.baseChange hφ f).s.left ≫
        (toSheaf.map (pullback.fst φ f).left ≫ P.quotientMap) :=
  sorry

/-- The second projection of the comparison iso is the descent of `U' ⟶ U ⟶ U/R`. -/
theorem quotientSheafBaseChangeIso_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.quotientSheafBaseChangeIso hφ f).hom ≫
        pullback.snd (toSheaf.map f.left) (P.quotientSheafFactor hφ) =
      (P.baseChange hφ f).quotientSheafLift
        (toSheaf.map (pullback.fst φ f).left ≫ P.quotientMap)
        (P.quotientMap_fst_equalizes hφ f) :=
  sorry

/-- The coequalizer triangle: `U' ⟶ U'/R' ⟶ X' ×_X U/R` recovers
`toQuotientSheafPullback`. -/
theorem toQuotientSheafPullback_comp_quotientMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.baseChange hφ f).quotientMap ≫ (P.quotientSheafBaseChangeIso hφ f).hom =
      P.toQuotientSheafPullback hφ f :=
  sorry


/-- The first projection of the presheaf comparison is the factor of the map to `X'`. -/
theorem quotientPresheafBaseChangeHom_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    P.quotientPresheafBaseChangeHom hφ f ≫
        pullback.fst (toSheaf.map f.left).hom (P.quotientPresheafFactor hφ) =
      (P.baseChange hφ f).quotientPresheafFactor (P.isInvariantHom_pullback_snd hφ f) :=
  sorry

/-- The hom of `quotientPresheafBaseChangeIso` is `quotientPresheafBaseChangeHom`. -/
theorem quotientPresheafBaseChangeIso_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.quotientPresheafBaseChangeIso hφ f).hom = P.quotientPresheafBaseChangeHom hφ f :=
  sorry

/-- The hom of `quotientSheafCospanIso` is `quotientSheafCospanMap`. -/
private theorem quotientSheafCospanIso_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X X' : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (f : X' ⟶ X) :
    (P.quotientSheafCospanIso hφ f).hom = P.quotientSheafCospanMap hφ f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
