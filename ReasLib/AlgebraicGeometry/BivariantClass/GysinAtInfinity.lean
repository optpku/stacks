/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Localization
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily.Section
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.BivariantClass.ZeroScheme
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.BivariantClass.Cospan.ProperPushforward

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.GysinAtInfinity

/-- The infinity divisor on the relative projective-line family `X ×ₛ ℙ¹ₛ`. -/
noncomputable def ambientInfinityDivisor {S : Scheme.{u}} (X : Over S) :
    (ProjectiveLineFamily.space X).IdealSheafData :=
  (ProjectiveLine.Relative.infinityDivisor S).comap
    (pullback.snd X.hom (ProjectiveSpace.toBase 1 S))

/-- The ambient infinity divisor is the pullback of the standard relative infinity divisor. -/
theorem ambientInfinityDivisor_def {S : Scheme.{u}} (X : Over S) :
    ambientInfinityDivisor X =
      (ProjectiveLine.Relative.infinityDivisor S).comap
        (pullback.snd X.hom (ProjectiveSpace.toBase 1 S)) := sorry

/-- The infinity divisor on a relative projective-line family is effective Cartier. -/
instance ambientInfinityDivisorIsEffectiveCartier {S : Scheme.{u}} (X : Over S) :
    IsEffectiveCartierDivisor (ambientInfinityDivisor X).subschemeι := sorry

/-- The sheaf associated to the ambient infinity divisor is invertible. -/
instance ambientInfinityLineBundleInvertible {S : Scheme.{u}} (X : Over S) :
    Scheme.Modules.Invertible (ambientInfinityDivisor X).associatedSheaf := sorry

/-- The affine-line part of `X ×ₛ ℙ¹ₛ`, obtained by removing the infinity divisor. -/
def affinePart {S : Scheme.{u}} (X : Over S) : (ProjectiveLineFamily.space X).Opens :=
  (ambientInfinityDivisor X).openComplement

/-- The affine part is the open complement of the ambient infinity divisor. -/
theorem affinePart_def {S : Scheme.{u}} (X : Over S) :
    affinePart X = (ambientInfinityDivisor X).openComplement := sorry

/-- The scheme `W`, regarded over `S` through `b : W ⟶ X ×ₛ ℙ¹ₛ`. -/
abbrev compactification {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) : Over S :=
  Over.mk (b ≫ ProjectiveLineFamily.toBase X)

/-- The structure map of the compactification is `b` followed by the projective-line-family
structure map. -/
theorem compactification_hom {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    (compactification X b).hom = b ≫ ProjectiveLineFamily.toBase X := sorry

/-- The first projection after `b` is a morphism from `W` to `X` over `S`. -/
theorem toX_fac {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    (b ≫ pullback.fst X.hom (ProjectiveSpace.toBase 1 S)) ≫ X.hom =
      (compactification X b).hom := sorry

/-- The morphism `W ⟶ X` induced by the first projection of `X ×ₛ ℙ¹ₛ`. -/
def toX {S W : Scheme.{u}} (X : Over S) (b : W ⟶ ProjectiveLineFamily.space X) :
    compactification X b ⟶ Over.mk X.hom :=
  Over.homMk (b ≫ pullback.fst X.hom (ProjectiveSpace.toBase 1 S)) (toX_fac X b)

/-- The underlying map of `toX X b` is the first projection after `b`. -/
theorem toX_left {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    (toX X b).left = b ≫ pullback.fst X.hom (ProjectiveSpace.toBase 1 S) := sorry

/-- The line bundle whose pulled-back canonical section cuts out the infinity fibre on `W`. -/
noncomputable def infinityLineBundle {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) : W.Modules :=
  (Scheme.Modules.pullback b).obj (ambientInfinityDivisor X).associatedSheaf

/-- Pullback preserves invertibility of the infinity line bundle. -/
instance infinityLineBundleInvertible {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    Scheme.Modules.Invertible (infinityLineBundle X b) := sorry

/-- The canonical pulled-back section cutting out the infinity fibre on `W`. -/
noncomputable def infinitySection {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) : (infinityLineBundle X b).sections :=
  Scheme.Modules.sectionsPullback b (ambientInfinityDivisor X).associatedSheaf
    (ambientInfinityDivisor X).canonicalSection

/-- The scheme-theoretic inverse image on `W` of the infinity divisor. -/
noncomputable def infinityDivisor {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) : W.IdealSheafData :=
  Scheme.zeroIdealSheaf (infinityLineBundle X b) (infinitySection X b)

/-- The zero-scheme description of the infinity fibre agrees with ideal-sheaf pullback. -/
theorem infinityDivisor_eq_comap {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    infinityDivisor X b = (ambientInfinityDivisor X).comap b := sorry

/-- The inverse image `W∞`, bundled with its structure morphism to `S`. -/
abbrev infinityFiber {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) : Over S :=
  Over.mk ((infinityDivisor X b).subschemeι ≫ (compactification X b).hom)

/-- The structure morphism of the infinity fibre factors through `W`. -/
theorem infinityFiber_hom {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    (infinityFiber X b).hom =
      (infinityDivisor X b).subschemeι ≫ (compactification X b).hom := sorry

/-- The canonical closed immersion `i∞ : W∞ ⟶ W`, viewed over `S`. -/
def infinityInclusion {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    infinityFiber X b ⟶ compactification X b :=
  Over.homMk (infinityDivisor X b).subschemeι

/-- The underlying map of the infinity inclusion is the zero-scheme inclusion. -/
theorem infinityInclusion_left {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    (infinityInclusion X b).left = (infinityDivisor X b).subschemeι := sorry

/-- The morphism `W∞ ⟶ X` whose degree-zero bivariant class is constructed below. -/
def infinityToX {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    infinityFiber X b ⟶ Over.mk X.hom :=
  infinityInclusion X b ≫ toX X b

/-- The map from the infinity fibre to `X` is the evident composite through `W`. -/
theorem infinityToX_def {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    infinityToX X b = infinityInclusion X b ≫ toX X b := sorry

/-- A proper compactification is locally of finite type over the base. -/
instance compactificationLocallyOfFiniteType {S W : Scheme.{u}} (X : Over S)
    [LocallyOfFiniteType X.hom] (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] :
    LocallyOfFiniteType (compactification X b).hom := sorry

/-- The infinity fibre of a proper compactification is locally of finite type over the base. -/
instance infinityFiberLocallyOfFiniteType {S W : Scheme.{u}} (X : Over S)
    [LocallyOfFiniteType X.hom] (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] :
    LocallyOfFiniteType (infinityFiber X b).hom := sorry

/-- The induced map from a proper compactification to `X` is proper. -/
instance toXIsProper {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] :
    IsProper (toX X b).left := sorry

/-- The infinity-fibre inclusion is proper. -/
instance infinityInclusionIsProper {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) :
    IsProper (infinityInclusion X b).left := sorry

/-- The zero section lies in the affine complement of the infinity divisor. -/
theorem zeroSection_range_affine {S : Scheme.{u}} (X : Over S) :
    Set.range (ProjectiveLineFamily.zeroSection X).base ⊆
      Set.range (affinePart X).ι.base := sorry

/-- The zero section, factored through the affine part of the projective-line family. -/
noncomputable def zeroToAffine {S : Scheme.{u}} (X : Over S) :
    X.left ⟶ (affinePart X).toScheme :=
  IsOpenImmersion.lift (affinePart X).ι (ProjectiveLineFamily.zeroSection X)
    (zeroSection_range_affine X)

/-- The affine factorization of the zero section recovers the original zero section. -/
theorem zeroToAffine_comp_ι {S : Scheme.{u}} (X : Over S) :
    zeroToAffine X ≫ (affinePart X).ι = ProjectiveLineFamily.zeroSection X := sorry

/-- The lift of the zero section to `W`, using the inverse over the affine part. -/
noncomputable def zeroSectionLiftScheme {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsIso (b ∣_ affinePart X)] : X.left ⟶ W :=
  zeroToAffine X ≫ inv (b ∣_ affinePart X) ≫ (b ⁻¹ᵁ affinePart X).ι

/-- The lifted zero section maps under `b` to the projective-line zero section. -/
theorem zeroSectionLiftScheme_comp_b {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsIso (b ∣_ affinePart X)] :
    zeroSectionLiftScheme X b ≫ b = ProjectiveLineFamily.zeroSection X := sorry

/-- The lifted zero section is compatible with the structure maps to `S`. -/
theorem zeroSectionLift_fac {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsIso (b ∣_ affinePart X)] :
    zeroSectionLiftScheme X b ≫ (compactification X b).hom = X.hom := sorry

/-- The canonical lift `i₀ : X ⟶ W` of the zero section, viewed over `S`. -/
noncomputable def zeroSectionLift {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [h_b : IsIso (b ∣_ affinePart X)] :
    Over.mk X.hom ⟶ compactification X b :=
  Over.homMk (@zeroSectionLiftScheme S W X b h_b) (@zeroSectionLift_fac S W X b h_b)

/-- The lifted zero section is a section of `W ⟶ X`. -/
theorem zeroSectionLift_toX {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsIso (b ∣_ affinePart X)] :
    zeroSectionLift X b ≫ toX X b = 𝟙 (Over.mk X.hom) := sorry

/-- The lifted zero section is proper. -/
instance zeroSectionLiftIsProper {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsIso (b ∣_ affinePart X)] :
    IsProper (zeroSectionLift X b).left := sorry

/-- The identity bivariant class, transported to the composite `X ⟶ W ⟶ X`. -/
def zeroIdentity {S W : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] [IsIso (b ∣_ affinePart X)] :
    BivariantClass δ (zeroSectionLift X b ≫ toX X b) 0 :=
  (zeroSectionLift_toX X b).symm ▸ ChowCohomology.one δ X.hom

/-- `zeroIdentity` is transport of the degree-zero identity class along the section equation. -/
theorem zeroIdentity_def {S W : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] [IsIso (b ∣_ affinePart X)] :
    zeroIdentity δ X b =
      (zeroSectionLift_toX X b).symm ▸ ChowCohomology.one δ X.hom := sorry

/-- The pullback of `W ⟶ X` along a displayed base-change map. -/
abbrev baseChange {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {Y' : Over S} (g : Y' ⟶ Over.mk X.hom) :
    Over S :=
  pullback (toX X b) g

/-- The base-changed compactification has the canonical pullback structure map. -/
theorem baseChange_hom {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {Y' : Over S} (g : Y' ⟶ Over.mk X.hom) :
    (baseChange X b g).hom = (pullback (toX X b) g).hom := sorry

/-- The outer cartesian square determines a map into the pullback compactification. -/
theorem baseChangeLift_fac {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {X' Y' : Over S}
    (i : X' ⟶ infinityFiber X b) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk X.hom)
    (square : IsPullback i.left f'.left (infinityToX X b).left g.left) :
    (i ≫ infinityInclusion X b) ≫ toX X b = f' ≫ g := sorry

/-- The canonical map from the pulled-back infinity fibre to the pulled-back compactification. -/
noncomputable def baseChangeLift {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {X' Y' : Over S}
    (i : X' ⟶ infinityFiber X b) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk X.hom)
    (square : IsPullback i.left f'.left (infinityToX X b).left g.left) :
    X' ⟶ baseChange X b g :=
  pullback.lift (i ≫ infinityInclusion X b) f' (baseChangeLift_fac X b i f' g square)

/-- The infinity-fibre square inside the base-changed compactification is cartesian. -/
theorem baseChangeInfinitySquare {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {X' Y' : Over S}
    (i : X' ⟶ infinityFiber X b) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk X.hom)
    (square : IsPullback i.left f'.left (infinityToX X b).left g.left) :
    IsPullback i.left (baseChangeLift X b i f' g square).left
      (infinityInclusion X b).left (pullback.fst (toX X b) g).left := sorry

/-- The affine open of a base-changed compactification. -/
def baseChangeOpen {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {Y' : Over S} (g : Y' ⟶ Over.mk X.hom) :
    (baseChange X b g).left.Opens :=
  ((pullback.fst (toX X b) g).left ≫ b) ⁻¹ᵁ affinePart X

/-- The base-changed affine open is the inverse image of `affinePart X`. -/
theorem baseChangeOpen_def {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {Y' : Over S} (g : Y' ⟶ Over.mk X.hom) :
    baseChangeOpen X b g =
      ((pullback.fst (toX X b) g).left ≫ b) ⁻¹ᵁ affinePart X := sorry

/-- The base-changed affine open, bundled over `S`. -/
abbrev baseChangeAffine {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {Y' : Over S} (g : Y' ⟶ Over.mk X.hom) :
    Over S :=
  Over.mk ((baseChangeOpen X b g).ι ≫ (baseChange X b g).hom)

/-- The affine-open projection to the base-change scheme respects structure maps. -/
theorem baseChangeAffineProjection_fac {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {Y' : Over S} (g : Y' ⟶ Over.mk X.hom) :
    ((baseChangeOpen X b g).ι ≫ (pullback.snd (toX X b) g).left) ≫ Y'.hom =
      (baseChangeAffine X b g).hom := sorry

/-- The projection from the affine open of the base-changed compactification to `Y'`. -/
def baseChangeAffineProjection {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {Y' : Over S} (g : Y' ⟶ Over.mk X.hom) :
    baseChangeAffine X b g ⟶ Y' :=
  Over.homMk ((baseChangeOpen X b g).ι ≫ (pullback.snd (toX X b) g).left)
    (baseChangeAffineProjection_fac X b g)

/-- Base change of a proper compactification remains locally of finite type over `S`. -/
instance baseChangeLocallyOfFiniteType {S W : Scheme.{u}} (X : Over S)
    [LocallyOfFiniteType X.hom] (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    {Y' : Over S} [LocallyOfFiniteType Y'.hom] (g : Y' ⟶ Over.mk X.hom) :
    LocallyOfFiniteType (baseChange X b g).hom := sorry

/-- The affine open of a base-changed compactification is locally of finite type over `S`. -/
instance baseChangeAffineLocallyOfFiniteType {S W : Scheme.{u}} (X : Over S)
    [LocallyOfFiniteType X.hom] (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    {Y' : Over S} [LocallyOfFiniteType Y'.hom] (g : Y' ⟶ Over.mk X.hom) :
    LocallyOfFiniteType (baseChangeAffine X b g).hom := sorry

/-- Over the affine part, the base-changed compactification projection is flat. -/
instance baseChangeAffineProjectionFlat {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsIso (b ∣_ affinePart X)]
    {Y' : Over S} (g : Y' ⟶ Over.mk X.hom) :
    Flat (baseChangeAffineProjection X b g).left := sorry

/-- Over the affine part, the base-changed compactification has relative dimension one. -/
theorem baseChangeAffineProjectionRelativeDimension {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsIso (b ∣_ affinePart X)]
    {Y' : Over S} (g : Y' ⟶ Over.mk X.hom) :
    Scheme.Hom.RelativeDimension (baseChangeAffineProjection X b g).left 1 := sorry

/-- The first projection in the base-change square is locally of finite type when the
base-change map is locally of finite type. -/
instance baseChangeFstLocallyOfFiniteType {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) {Y' : Over S} (g : Y' ⟶ Over.mk X.hom)
    [LocallyOfFiniteType g.left] :
    LocallyOfFiniteType (pullback.fst (toX X b) g).left := sorry

/-- The grading identity for flat pullback followed by the infinity Gysin map. -/
theorem gysinDegree (k : ℤ) : (k + 1) - 1 = k := sorry

/-- Gysin pullback from a base-changed compactification to its displayed infinity fibre. -/
noncomputable def baseChangeGysin
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ infinityFiber X b) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk X.hom)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (infinityToX X b).left g.left) (k : ℤ) :
    RelativeChow δ (baseChange X b g) (k + 1) →+ RelativeChow δ X' k :=
  (ChowCohomology.castDegree δ (gysinDegree k)).comp
    (gysinCap δ (compactification X b) (infinityLineBundle X b) (infinitySection X b)
      i (baseChangeLift X b i f' g square) (pullback.fst (toX X b) g)
      (baseChangeInfinitySquare X b i f' g square) (k + 1))

/-- Infinity Gysin kills the closed-complement term in the localization complex. -/
theorem baseChangeGysin_vanishes
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ infinityFiber X b) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk X.hom)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (infinityToX X b).left g.left) (k : ℤ) :
    (ChowGroup.Localization.complex (baseChange X b g).hom δ
      (baseChangeOpen X b g) (k + 1)).f ≫
        AddCommGrpCat.ofHom (baseChangeGysin δ X b i f' g square k) = 0 := sorry

/-- The canonical map descended from infinity Gysin through Chow localization. -/
noncomputable def descent
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ infinityFiber X b) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk X.hom)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (infinityToX X b).left g.left) (k : ℤ) :
    RelativeChow δ (baseChangeAffine X b g) (k + 1) →+ RelativeChow δ X' k :=
  ((ChowGroup.Localization.exact (baseChange X b g).hom δ
      (baseChangeOpen X b g) (k + 1)).1.desc
        (AddCommGrpCat.ofHom (baseChangeGysin δ X b i f' g square k))
        (baseChangeGysin_vanishes δ X b i f' g square k)).hom

/-- The descended map recovers infinity Gysin after open restriction. -/
theorem openPullback_comp_descent
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ infinityFiber X b) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk X.hom)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (infinityToX X b).left g.left) (k : ℤ) :
    (descent δ X b i f' g square k).comp
        (ChowGroup.Localization.openPullback (baseChange X b g).hom δ
          (baseChangeOpen X b g) (k + 1)) = baseChangeGysin δ X b i f' g square k := sorry

/-- The degree-zero cap family obtained by affine-line pullback and localization descent. -/
noncomputable def cap
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] [IsIso (b ∣_ affinePart X)] :
    CapFamily δ (infinityToX X b) 0 :=
  fun {_ Y'} _ _ i f' g _ square k ↦
    (ChowCohomology.castDegree δ (Int.sub_zero k).symm).comp
      ((descent δ X b i f' g square k).comp
        (@ChowGroup.flatPullback S _ δ _ (baseChangeAffine X b g) Y' _ _
          (baseChangeAffineProjection X b g) 1 _
          (baseChangeAffineProjectionRelativeDimension X b g) k))

/-- Evaluation of `cap` is affine-line flat pullback followed by localization descent. -/
theorem cap_apply
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] [IsIso (b ∣_ affinePart X)]
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ infinityFiber X b) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk X.hom)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (infinityToX X b).left g.left) (k : ℤ) :
    cap δ X b i f' g square k =
      (ChowCohomology.castDegree δ (Int.sub_zero k).symm).comp
        ((descent δ X b i f' g square k).comp
          (@ChowGroup.flatPullback S _ δ _ (baseChangeAffine X b g) Y' _ _
            (baseChangeAffineProjection X b g) 1 _
            (baseChangeAffineProjectionRelativeDimension X b g) k)) := sorry

/-- The Gysin-at-infinity cap family commutes with proper pushforward. -/
theorem cap_mapProper
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] [IsIso (b ∣_ affinePart X)] :
    CompatibleWithProperPushforward δ (cap δ X b) := sorry

/-- The Gysin-at-infinity cap family commutes with flat pullback. -/
theorem cap_pullbackFlat
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] [IsIso (b ∣_ affinePart X)] :
    CompatibleWithFlatPullback δ (cap δ X b) := sorry

/-- The Gysin-at-infinity cap family commutes with effective-Cartier Gysin pullback. -/
theorem cap_gysinCartier
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] [IsIso (b ∣_ affinePart X)] :
    CompatibleWithCartierGysin δ (cap δ X b) := sorry

end AlgebraicGeometry.BivariantClass.GysinAtInfinity

namespace AlgebraicGeometry.BivariantClass

/-- The canonical degree-zero bivariant class produced by Gysin pullback at infinity. -/
noncomputable def gysinAtInfinity
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ GysinAtInfinity.affinePart X)] :
    BivariantClass δ (GysinAtInfinity.infinityToX X b) 0 where
  cap := fun {_ _} _ _ i f' g _ square k ↦
    GysinAtInfinity.cap δ X b i f' g square k
  map_proper := GysinAtInfinity.cap_mapProper δ X b
  pullback_flat := GysinAtInfinity.cap_pullbackFlat δ X b
  gysin_cartier := GysinAtInfinity.cap_gysinCartier δ X b

/-- Evaluation of `gysinAtInfinity` uses the localization-descended cap family. -/
theorem gysinAtInfinity_cap
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ GysinAtInfinity.affinePart X)]
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ GysinAtInfinity.infinityFiber X b) (f' : X' ⟶ Y')
    (g : Y' ⟶ Over.mk X.hom) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left
      (GysinAtInfinity.infinityToX X b).left g.left) (k : ℤ) :
    (gysinAtInfinity δ X b).cap i f' g square k =
      GysinAtInfinity.cap δ X b i f' g square k := sorry

namespace GysinAtInfinity

/-- The cap family obtained by applying proper pushforward to the Gysin-at-infinity
class along the infinity-fibre inclusion. -/
noncomputable def infinityPushforwardCap
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ affinePart X)] :
    CapFamily δ (toX X b) 0 :=
  fun {W' X'} hW' hX' i f' g hg square k ↦
    let baseChangeSquare :
        IsPullback (pullback.fst (infinityInclusion X b) i).left
          (pullback.snd (infinityInclusion X b) i).left
          (infinityInclusion X b).left i.left :=
      (IsPullback.of_hasPullback (infinityInclusion X b) i).map (Over.forget S)
    let h_i : LocallyOfFiniteType i.left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback square.flip hg
    let h_fst : LocallyOfFiniteType
        (pullback.fst (infinityInclusion X b) i).left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback baseChangeSquare.flip h_i
    let h_pullback : LocallyOfFiniteType
        (pullback (infinityInclusion X b) i).hom :=
      (pullback.snd (infinityInclusion X b) i).w ▸
        @locallyOfFiniteType_comp _ _ _
          (pullback.snd (infinityInclusion X b) i).left W'.hom
          (MorphismProperty.IsStableUnderBaseChange.of_isPullback baseChangeSquare
            (inferInstance : IsProper (infinityInclusion X b).left)).toLocallyOfFiniteType
          hW'
    (@Cospan.properPushforwardCap S _ δ _
      (compactification X b) (infinityFiber X b) _ _
      (infinityInclusion X b) _
      W' W' (pullback (infinityInclusion X b) i)
      hW' hW' h_pullback i h_i i (𝟙 W') IsPullback.of_id_snd
      (pullback.fst (infinityInclusion X b) i) h_fst
      (pullback.snd (infinityInclusion X b) i) baseChangeSquare k).comp
        ((Cospan.castDegree δ (Int.sub_zero k)).comp
          (@(gysinAtInfinity δ X b).cap
            (pullback (infinityInclusion X b) i) X' h_pullback hX'
            (pullback.fst (infinityInclusion X b) i)
            (pullback.snd (infinityInclusion X b) i ≫ f') g hg
            (baseChangeSquare.paste_vert square) k))

/-- Evaluation of the infinity-side pushed cap family is Gysin-at-infinity followed by
the canonical cospan proper pushforward. -/
theorem infinityPushforwardCap_apply
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ affinePart X)]
    {W' X' : Over S} [LocallyOfFiniteType W'.hom] [LocallyOfFiniteType X'.hom]
    (i : W' ⟶ compactification X b) [LocallyOfFiniteType i.left]
    (f' : W' ⟶ X') (g : X' ⟶ Over.mk X.hom) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (toX X b).left g.left)
    [LocallyOfFiniteType (pullback (infinityInclusion X b) i).hom]
    [LocallyOfFiniteType (pullback.fst (infinityInclusion X b) i).left]
    (baseChangeSquare :
      IsPullback (pullback.fst (infinityInclusion X b) i).left
        (pullback.snd (infinityInclusion X b) i).left
        (infinityInclusion X b).left i.left)
    (k : ℤ) (α : RelativeChow δ X' k) :
    infinityPushforwardCap δ X b i f' g square k α =
      Cospan.properPushforwardCap δ (infinityInclusion X b)
        i i (𝟙 W') IsPullback.of_id_snd
        (pullback.fst (infinityInclusion X b) i)
        (pullback.snd (infinityInclusion X b) i) baseChangeSquare k
        (Cospan.castDegree δ (Int.sub_zero k)
          ((gysinAtInfinity δ X b).cap
            (pullback.fst (infinityInclusion X b) i)
            (pullback.snd (infinityInclusion X b) i ≫ f') g
            (baseChangeSquare.paste_vert square) k α)) := sorry

/-- The cap family obtained by applying proper pushforward to the transported identity
class along the lifted zero section. -/
noncomputable def zeroPushforwardCap
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ affinePart X)] :
    CapFamily δ (toX X b) 0 :=
  fun {W' X'} hW' hX' i f' g hg square k ↦
    let baseChangeSquare :
        IsPullback (pullback.fst (zeroSectionLift X b) i).left
          (pullback.snd (zeroSectionLift X b) i).left
          (zeroSectionLift X b).left i.left :=
      (IsPullback.of_hasPullback (zeroSectionLift X b) i).map (Over.forget S)
    let h_i : LocallyOfFiniteType i.left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback square.flip hg
    let h_fst : LocallyOfFiniteType
        (pullback.fst (zeroSectionLift X b) i).left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback baseChangeSquare.flip h_i
    let h_pullback : LocallyOfFiniteType (pullback (zeroSectionLift X b) i).hom :=
      (pullback.snd (zeroSectionLift X b) i).w ▸
        @locallyOfFiniteType_comp _ _ _
          (pullback.snd (zeroSectionLift X b) i).left W'.hom
          (MorphismProperty.IsStableUnderBaseChange.of_isPullback baseChangeSquare
            (inferInstance : IsProper (zeroSectionLift X b).left)).toLocallyOfFiniteType
          hW'
    (@Cospan.properPushforwardCap S _ δ _
      (compactification X b) (Over.mk X.hom) _ _
      (zeroSectionLift X b) _
      W' W' (pullback (zeroSectionLift X b) i)
      hW' hW' h_pullback i h_i i (𝟙 W') IsPullback.of_id_snd
      (pullback.fst (zeroSectionLift X b) i) h_fst
      (pullback.snd (zeroSectionLift X b) i) baseChangeSquare k).comp
        ((Cospan.castDegree δ (Int.sub_zero k)).comp
          (@(zeroIdentity δ X b).cap
            (pullback (zeroSectionLift X b) i) X' h_pullback hX'
            (pullback.fst (zeroSectionLift X b) i)
            (pullback.snd (zeroSectionLift X b) i ≫ f') g hg
            (baseChangeSquare.paste_vert square) k))

/-- Evaluation of the zero-side pushed cap family is the transported identity action
followed by the canonical cospan proper pushforward. -/
theorem zeroPushforwardCap_apply
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ affinePart X)]
    {W' X' : Over S} [LocallyOfFiniteType W'.hom] [LocallyOfFiniteType X'.hom]
    (i : W' ⟶ compactification X b) [LocallyOfFiniteType i.left]
    (f' : W' ⟶ X') (g : X' ⟶ Over.mk X.hom) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (toX X b).left g.left)
    [LocallyOfFiniteType (pullback (zeroSectionLift X b) i).hom]
    [LocallyOfFiniteType (pullback.fst (zeroSectionLift X b) i).left]
    (baseChangeSquare :
      IsPullback (pullback.fst (zeroSectionLift X b) i).left
        (pullback.snd (zeroSectionLift X b) i).left
        (zeroSectionLift X b).left i.left)
    (k : ℤ) (α : RelativeChow δ X' k) :
    zeroPushforwardCap δ X b i f' g square k α =
      Cospan.properPushforwardCap δ (zeroSectionLift X b)
        i i (𝟙 W') IsPullback.of_id_snd
        (pullback.fst (zeroSectionLift X b) i)
        (pullback.snd (zeroSectionLift X b) i) baseChangeSquare k
        (Cospan.castDegree δ (Int.sub_zero k)
          ((zeroIdentity δ X b).cap
            (pullback.fst (zeroSectionLift X b) i)
            (pullback.snd (zeroSectionLift X b) i ≫ f') g
            (baseChangeSquare.paste_vert square) k α)) := sorry

end GysinAtInfinity

/-- Proper pushforward of the Gysin-at-infinity cap family along the infinity fibre
equals proper pushforward of the identity cap family along the lifted zero section. -/
theorem gysinAtInfinity_pushforward
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ GysinAtInfinity.affinePart X)] :
    (GysinAtInfinity.infinityPushforwardCap δ X b :
        CapFamily δ (GysinAtInfinity.toX X b) 0) =
      (GysinAtInfinity.zeroPushforwardCap δ X b :
        CapFamily δ (GysinAtInfinity.toX X b) 0) := sorry

/-- The proper-pushforward identity for Gysin at infinity, evaluated after any
locally finite-type base change and on any relative Chow class. -/
theorem gysinAtInfinity_pushforward_apply
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ GysinAtInfinity.affinePart X)]
    {W' X' : Over S} [LocallyOfFiniteType W'.hom] [LocallyOfFiniteType X'.hom]
    (i : W' ⟶ GysinAtInfinity.compactification X b) (f' : W' ⟶ X')
    (g : X' ⟶ Over.mk X.hom) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (GysinAtInfinity.toX X b).left g.left)
    (k : ℤ) (α : RelativeChow δ X' k) :
    GysinAtInfinity.infinityPushforwardCap δ X b i f' g square k α =
      GysinAtInfinity.zeroPushforwardCap δ X b i f' g square k α := sorry

end AlgebraicGeometry.BivariantClass
